import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity
import Mathlib.Analysis.Complex.RealDeriv

namespace ConnesWeilRH.Dev

open scoped Topology
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def familyDeficit2345 (radius position : ℝ) : ℝ :=
  1 - (position / radius) ^ 2

noncomputable def familyLog2345 (radius position : ℝ) : ℝ :=
  -30 / familyDeficit2345 radius position

noncomputable def familyLogFirst2345 (radius position : ℝ) : ℝ :=
  -60 * (position / radius) * (familyDeficit2345 radius position)⁻¹ ^ 2 / radius

noncomputable def familyLogSecond2345 (radius position : ℝ) : ℝ :=
  -60 * ((familyDeficit2345 radius position)⁻¹ ^ 2 +
    4 * (position / radius) ^ 2 * (familyDeficit2345 radius position)⁻¹ ^ 3) / radius ^ 2

noncomputable def familyInterior2345 (coefficient : ℂ) (modulation radius : ℝ)
    (position : ℝ) : ℂ :=
  coefficient * Complex.exp ((familyLog2345 radius position : ℂ) +
    (modulation * position : ℝ) * Complex.I)

noncomputable def familyFirstFactor2345 (modulation radius position : ℝ) : ℂ :=
  (familyLogFirst2345 radius position : ℂ) + (modulation : ℂ) * Complex.I

noncomputable def familySecondFactor2345 (modulation radius position : ℝ) : ℂ :=
  ((familyLogSecond2345 radius position + (familyLogFirst2345 radius position) ^ 2 -
    modulation ^ 2 : ℝ) : ℂ) +
    (2 * modulation * familyLogFirst2345 radius position : ℝ) * Complex.I

theorem familyDeficit2345_pos {radius position : ℝ} (hradius : 0 < radius)
    (hinside : |position| < radius) : 0 < familyDeficit2345 radius position := by
  have hratio : |position / radius| < 1 := by
    rw [abs_div, abs_of_pos hradius, div_lt_one hradius]
    exact hinside
  unfold familyDeficit2345
  nlinarith [sq_abs (position / radius), abs_nonneg (position / radius)]

theorem familyDeficit2345_hasDerivAt (radius position : ℝ) :
    HasDerivAt (familyDeficit2345 radius) (-2 * (position / radius) / radius) position := by
  convert (hasDerivAt_const position (1 : ℝ)).sub
    (((hasDerivAt_id position).div_const radius).pow 2) using 1 <;>
    dsimp [familyDeficit2345] <;> ring

theorem familyLog2345_hasDerivAt {radius position : ℝ} (hradius : radius ≠ 0)
    (hdeficit : familyDeficit2345 radius position ≠ 0) :
    HasDerivAt (familyLog2345 radius) (familyLogFirst2345 radius position) position := by
  convert (hasDerivAt_const position (-30 : ℝ)).div
    (familyDeficit2345_hasDerivAt radius position) hdeficit using 1
  unfold familyLogFirst2345
  field_simp
  <;> ring

theorem familyLogFirst2345_hasDerivAt {radius position : ℝ} (hradius : radius ≠ 0)
    (hdeficit : familyDeficit2345 radius position ≠ 0) :
    HasDerivAt (familyLogFirst2345 radius) (familyLogSecond2345 radius position) position := by
  have hinv := (familyDeficit2345_hasDerivAt radius position).inv hdeficit
  convert (((hasDerivAt_const position (-60 : ℝ)).mul
    ((hasDerivAt_id position).div_const radius)).mul (hinv.pow 2)).div_const radius using 1
  dsimp [familyLogSecond2345]
  field_simp
  <;> ring

theorem familyInterior2345_hasDerivAt {radius position : ℝ}
    (coefficient : ℂ) (modulation : ℝ) (hradius : radius ≠ 0)
    (hdeficit : familyDeficit2345 radius position ≠ 0) :
    HasDerivAt (familyInterior2345 coefficient modulation radius)
      (familyInterior2345 coefficient modulation radius position *
        familyFirstFactor2345 modulation radius position) position := by
  have hlog := (familyLog2345_hasDerivAt hradius hdeficit).ofReal_comp
  have hphase := ((hasDerivAt_id position).const_mul modulation).ofReal_comp.mul_const Complex.I
  convert ((hlog.add hphase).cexp).const_mul coefficient using 1
  dsimp [familyInterior2345, familyFirstFactor2345]
  ring

theorem familyFirstFactor2345_hasDerivAt {radius position : ℝ}
    (modulation : ℝ) (hradius : radius ≠ 0)
    (hdeficit : familyDeficit2345 radius position ≠ 0) :
    HasDerivAt (familyFirstFactor2345 modulation radius)
      (familyLogSecond2345 radius position : ℂ) position := by
  simpa only [familyFirstFactor2345, add_zero] using
    ((familyLogFirst2345_hasDerivAt hradius hdeficit).ofReal_comp).add
      (hasDerivAt_const position ((modulation : ℂ) * Complex.I))

theorem familySecondFactor2345_eq (modulation radius position : ℝ) :
    familySecondFactor2345 modulation radius position =
      (familyFirstFactor2345 modulation radius position) ^ 2 +
        (familyLogSecond2345 radius position : ℂ) := by
  simp only [familySecondFactor2345, familyFirstFactor2345,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  calc
    _ = (familyLogFirst2345 radius position : ℂ) ^ 2 +
        2 * (modulation : ℂ) * (familyLogFirst2345 radius position : ℂ) * Complex.I +
        (modulation : ℂ) ^ 2 * Complex.I ^ 2 +
        (familyLogSecond2345 radius position : ℂ) := by rw [Complex.I_sq]; ring
    _ = _ := by ring

theorem familyInterior2345_firstProduct_hasDerivAt {radius position : ℝ}
    (coefficient : ℂ) (modulation : ℝ) (hradius : radius ≠ 0)
    (hdeficit : familyDeficit2345 radius position ≠ 0) :
    HasDerivAt (fun coordinate => familyInterior2345 coefficient modulation radius coordinate *
      familyFirstFactor2345 modulation radius coordinate)
      (familyInterior2345 coefficient modulation radius position *
        familySecondFactor2345 modulation radius position) position := by
  convert (familyInterior2345_hasDerivAt coefficient modulation hradius hdeficit).mul
    (familyFirstFactor2345_hasDerivAt modulation hradius hdeficit) using 1
  rw [familySecondFactor2345_eq]
  ring

theorem externalFamilyValue2344_hasDerivAt_inside {radius position : ℝ}
    (coefficient : ℂ) (modulation : ℝ) (hradius : 0 < radius)
    (hinside : |position| < radius) :
    HasDerivAt (externalFamilyValue2344 coefficient modulation radius)
      (familyInterior2345 coefficient modulation radius position *
        familyFirstFactor2345 modulation radius position) position := by
  apply (familyInterior2345_hasDerivAt coefficient modulation (ne_of_gt hradius)
    (ne_of_gt (familyDeficit2345_pos hradius hinside))).congr_of_eventuallyEq
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hinside]
    with coordinate hcoordinate
  simp only [externalFamilyValue2344, if_pos hcoordinate, familyInterior2345,
    familyLog2345, familyDeficit2345]

theorem externalFamilyValue2344_secondDerivative_inside {radius position : ℝ}
    (coefficient : ℂ) (modulation : ℝ) (hradius : 0 < radius)
    (hinside : |position| < radius) :
    deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position =
      externalFamilyValue2344 coefficient modulation radius position *
        familySecondFactor2345 modulation radius position := by
  have heq : deriv (externalFamilyValue2344 coefficient modulation radius) =ᶠ[𝓝 position]
      (fun coordinate => familyInterior2345 coefficient modulation radius coordinate *
        familyFirstFactor2345 modulation radius coordinate) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hinside]
      with coordinate hcoordinate
    exact (externalFamilyValue2344_hasDerivAt_inside
      coefficient modulation hradius hcoordinate).deriv
  rw [heq.deriv_eq,
    (familyInterior2345_firstProduct_hasDerivAt coefficient modulation (ne_of_gt hradius)
      (ne_of_gt (familyDeficit2345_pos hradius hinside))).deriv]
  simp only [externalFamilyValue2344, if_pos hinside, familyInterior2345,
    familyLog2345, familyDeficit2345]

end ConnesWeilRH.Dev
