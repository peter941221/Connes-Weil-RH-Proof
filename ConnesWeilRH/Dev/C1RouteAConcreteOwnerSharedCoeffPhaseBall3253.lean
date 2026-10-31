import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedBumpBlock3247
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCorrelatedTaxiMiddlePoint3236

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped BigOperators

noncomputable def record2680Cell17168CoeffPhaseBall3253
    (family : Fin 30) : ComplexTaxiBall3235 :=
  (ComplexTaxiBall3235.point (record2680CorrectionCoefficient family)).mul
    (record2680MiddlePointPhaseBall3236
      (capturedModulations2584 family * record2680Center3212 17168) 9)

noncomputable def record2680Cell17168SharedCoeffPhaseBall3253 :
    ComplexTaxiBall3235 :=
  ComplexTaxiBall3235.sumFinset record2680Cell17168CoeffPhaseBall3253
    record2680Cell17168SharedFamilies3247

theorem complexTaxiBall3235_real_upper
    {ball : ComplexTaxiBall3235} {z : ℂ}
    (hz : ball.Mem z) : z.re ≤ ball.center.re + ball.radius := by
  have hdiff : |z.re - ball.center.re| ≤ ball.radius := by
    have htaxi := hz.2
    dsimp [taxiNorm3235] at htaxi
    linarith [abs_nonneg (z.im - ball.center.im)]
  have hle : z.re - ball.center.re ≤ ball.radius :=
    (le_abs_self (z.re - ball.center.re)).trans hdiff
  linarith

theorem record2680_cell17168_coeff_phase_ball_mem3253
    (family : Fin 30) :
    (record2680Cell17168CoeffPhaseBall3253 family).Mem
      (record2680CorrectionCoefficient family *
        Complex.exp (((capturedModulations2584 family *
          record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled :
      |(capturedModulations2584 family * record2680Center3212 17168) / 512| ≤ 1 := by
    fin_cases family <;>
      norm_num [capturedModulations2584, record2680Center3212,
        record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hphase := record2680_middle_point_phase_ball_mem3236 hscaled 9
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hphase
  rw [complex_phase_eq_pow512_3218]
  exact ComplexTaxiBall3235.mem_mul
    (ComplexTaxiBall3235.point_mem _) hphase

theorem record2680_cell17168_shared_coeff_phase_ball_mem3253 :
    record2680Cell17168SharedCoeffPhaseBall3253.Mem
      (∑ family ∈ record2680Cell17168SharedFamilies3247,
        record2680CorrectionCoefficient family *
          Complex.exp (((capturedModulations2584 family *
            record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  unfold record2680Cell17168SharedCoeffPhaseBall3253
  apply ComplexTaxiBall3235.mem_sumFinset
  intro family hfamily
  exact record2680_cell17168_coeff_phase_ball_mem3253 family

theorem record2680_cell17168_shared_coeff_phase_re_upper3253 :
    (∑ family ∈ record2680Cell17168SharedFamilies3247,
      record2680CorrectionCoefficient family *
        Complex.exp (((capturedModulations2584 family *
          record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)).re ≤
      record2680Cell17168SharedCoeffPhaseBall3253.center.re +
        record2680Cell17168SharedCoeffPhaseBall3253.radius := by
  exact complexTaxiBall3235_real_upper
    record2680_cell17168_shared_coeff_phase_ball_mem3253

end ConnesWeilRH.Dev
