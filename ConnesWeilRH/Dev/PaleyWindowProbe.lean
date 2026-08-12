import ConnesWeilRH.Dev.SoninWindowWitness
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Set
open scoped ENNReal

namespace ConnesWeilRH
namespace Dev
namespace PaleyWindow

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.SoninWindowWitness

/-- The Sonin window: a bounded open interval of the logarithmic carrier. -/
noncomputable def soninWindowIoo (lambda : CCM24SoninScale) : Set ℝ :=
  Set.Ioo (Real.log lambda) (Real.log lambda + Real.log 2)

@[simp] theorem measurableSet_soninWindowIoo (lambda : CCM24SoninScale) :
    MeasurableSet (soninWindowIoo lambda) :=
  measurableSet_Ioo

/-- The window is a bounded open interval, hence finite Lebesgue measure. -/
theorem soninWindowIoo_volume_ne_top (lambda : CCM24SoninScale) :
    volume (soninWindowIoo lambda) ≠ (⊤ : ℝ≥0∞) := by
  rw [soninWindowIoo, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The window has positive Lebesgue measure (length = log 2 > 0). -/
theorem soninWindowIoo_volume_ne_zero (lambda : CCM24SoninScale) :
    volume (soninWindowIoo lambda) ≠ 0 := by
  rw [soninWindowIoo, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by
    have hz : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith)

/-- The window has positive real Lebesgue measure. -/
theorem soninWindowIoo_measure_real_pos (lambda : CCM24SoninScale) :
    0 < (volume.real (soninWindowIoo lambda)) := by
  have hz : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [soninWindowIoo, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal]
  · linarith
  · linarith

/-- A nonzero candidate L2(R) element: constant 1 on the Sonin window. -/
noncomputable def soninWindowIndicator (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 :=
  indicatorConstLp 2 (measurableSet_soninWindowIoo lambda)
    (soninWindowIoo_volume_ne_top lambda) (1 : ℂ)

/-- Radial-support membership: t < log lambda forces the L2 value to vanish. -/
theorem soninWindowIndicator_mem_radial (lambda : CCM24SoninScale) :
    soninWindowIndicator lambda ∈ ccm24LogRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff lambda
    (soninWindowIndicator lambda)]
  filter_upwards [indicatorConstLp_coeFn_notMem (p := 2)
    (hs := measurableSet_soninWindowIoo lambda)
    (hμs := soninWindowIoo_volume_ne_top lambda)
    (c := (1 : ℂ))] with t hnot
  intro ht
  apply hnot
  intro hmem
  have hlt1 : Real.log lambda < t := hmem.1
  linarith

/-- The indicator is nonzero: it has positive L2 norm on the window. -/
theorem soninWindowIndicator_ne_zero (lambda : CCM24SoninScale) :
    soninWindowIndicator lambda ≠ 0 := by
  intro hzero
  have hnorm : ‖soninWindowIndicator lambda‖ = (0 : ℝ) := by
    rw [hzero]
    norm_num
  have hpos : (0 : ℝ) < ‖soninWindowIndicator lambda‖ := by
    unfold soninWindowIndicator
    rw [norm_indicatorConstLp' (p := 2) (by norm_num)
      (soninWindowIoo_volume_ne_zero lambda)]
    rw [norm_one, one_mul]
    exact Real.rpow_pos_of_pos (soninWindowIoo_measure_real_pos lambda)
      (1 / ENNReal.toReal 2)
  linarith

end PaleyWindow
end Dev
end ConnesWeilRH

