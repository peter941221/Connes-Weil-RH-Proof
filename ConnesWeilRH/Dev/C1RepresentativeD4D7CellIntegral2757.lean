import ConnesWeilRH.Dev.C1RepresentativeD4D7Boxes2755
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
noncomputable section

theorem representativeD4D7Cell_integral_bound2757 :
    (∫ x in representativeCell2736.lo..representativeCell2736.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        (representativeCell2736.hi - representativeCell2736.lo) *
          representativeD4Box2755.endpointAbsMax ∧
    (∫ x in representativeCell2736.lo..representativeCell2736.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        (representativeCell2736.hi - representativeCell2736.lo) *
          representativeD7Box2755.endpointAbsMax := by
  have hlo : 0 < representativeCell2736.lo := by
    norm_num [representativeCell2736]
  have hhi : representativeCell2736.hi < 1 := by
    norm_num [representativeCell2736]
  have hcont (n : ℕ) : Continuous (fun x : ℝ =>
      ‖iteratedDeriv n Real.smoothTransition x‖) :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous
  constructor
  · have hmono := intervalIntegral.integral_mono_on
      (f := fun x : ℝ => ‖iteratedDeriv 4 Real.smoothTransition x‖)
      (g := fun _ : ℝ => representativeD4Box2755.endpointAbsMax)
      (show representativeCell2736.lo ≤ representativeCell2736.hi by
        norm_num [representativeCell2736])
      (show IntervalIntegrable (fun x : ℝ =>
          ‖iteratedDeriv 4 Real.smoothTransition x‖) volume
          representativeCell2736.lo representativeCell2736.hi from
        (hcont 4).intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => representativeD4Box2755.endpointAbsMax)
          volume representativeCell2736.lo representativeCell2736.hi from
        continuous_const.intervalIntegrable _ _)
      (fun x hx => by
        have hmem := representativeD4Box_mem2755
          (show representativeCell2736.Mem x from hx)
        simpa only [Real.norm_eq_abs] using
          (abs_le_max_abs_abs hmem.1 hmem.2))
    have hconst :
        (∫ _u in representativeCell2736.lo..representativeCell2736.hi,
          representativeD4Box2755.endpointAbsMax) =
          (representativeCell2736.hi - representativeCell2736.lo) *
            representativeD4Box2755.endpointAbsMax := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at hmono
    exact hmono
  · have hmono := intervalIntegral.integral_mono_on
      (f := fun x : ℝ => ‖iteratedDeriv 7 Real.smoothTransition x‖)
      (g := fun _ : ℝ => representativeD7Box2755.endpointAbsMax)
      (show representativeCell2736.lo ≤ representativeCell2736.hi by
        norm_num [representativeCell2736])
      (show IntervalIntegrable (fun x : ℝ =>
          ‖iteratedDeriv 7 Real.smoothTransition x‖) volume
          representativeCell2736.lo representativeCell2736.hi from
        (hcont 7).intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => representativeD7Box2755.endpointAbsMax)
          volume representativeCell2736.lo representativeCell2736.hi from
        continuous_const.intervalIntegrable _ _)
      (fun x hx => by
        have hmem := representativeD7Box_mem2755
          (show representativeCell2736.Mem x from hx)
        simpa only [Real.norm_eq_abs] using
          (abs_le_max_abs_abs hmem.1 hmem.2))
    have hconst :
        (∫ _u in representativeCell2736.lo..representativeCell2736.hi,
          representativeD7Box2755.endpointAbsMax) =
          (representativeCell2736.hi - representativeCell2736.lo) *
            representativeD7Box2755.endpointAbsMax := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at hmono
    exact hmono

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
