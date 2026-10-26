import ConnesWeilRH.Dev.C1RouteBArchimedeanFourierReadback3121
import ConnesWeilRH.Dev.C1C3SigmaZeroMargin3090

namespace ConnesWeilRH.Source.C1RouteBArchimedeanFourierReadback3121

open ConnesWeilRH.Dev C1RouteBPrimeFourierReadback3120

theorem quarterPoint_zero3121 : quarterPoint3121 0 = 1 / 4 := by
  simp [quarterPoint3121, cyclePoint3120]

theorem reciprocal_first_zero3121 : reciprocal3121 0 0 = 2 := by
  norm_num [reciprocal3121, quarterPoint_zero3121]

theorem quarterPoint_avoids_poles3121 (n : ℕ) (xi : ℝ) :
    (n : ℂ) + quarterPoint3121 xi ≠ 0 := by
  apply ne_of_apply_ne Complex.re
  simp only [Complex.add_re, Complex.natCast_re, quarterPoint_re3121, Complex.zero_re]
  positivity

/-- Symbol guard only; no positivity of the owner's energy at zero is asserted. -/
theorem empty_kernel_not_everywhere_nonpos3121 :
    ¬ ∀ xi : ℝ, c3Sigma (2 * Real.pi * xi) + primeKernel3120 ∅ xi ≤ 0 := by
  intro h
  have hz := h 0
  simp only [mul_zero, primeKernel3120, Finset.sum_empty, add_zero] at hz
  exact (not_le_of_gt C1C3SigmaZeroMargin3090.c3Sigma_zero_pos) hz

end ConnesWeilRH.Source.C1RouteBArchimedeanFourierReadback3121

open ConnesWeilRH.Source.C1RouteBArchimedeanFourierReadback3121

#check poweredFamily_complete_gate_readback3121
#check poweredFamily_complete_gate_integrable3121
#print axioms weightedEnergy_integrable3121
#print axioms quarterPoint_re3121
#print axioms norm_reciprocal_le3121
#print axioms reciprocal_energy_integrable3121
#print axioms summable_integral_norm_reciprocal_energy3121
#print axioms summable_reciprocal3121
#print axioms sigma_eq_reciprocal_series3121
#print axioms cycle_resolvent_readback3121
#print axioms reciprocal_sum_integrable3121
#print axioms sigma_energy_integrable3121
#print axioms exp_test_integrable3121
#print axioms profile_integral_re3121
#print axioms integral_sigma_eq_series3121
#print axioms archimedean_eq_sigma_energy3121
#print axioms complete_gate_readback3121
#print axioms complete_gate_integrable3121
#print axioms poweredFamily_complete_gate_readback3121
#print axioms poweredFamily_complete_gate_integrable3121
#print axioms quarterPoint_zero3121
#print axioms reciprocal_first_zero3121
#print axioms quarterPoint_avoids_poles3121
#print axioms empty_kernel_not_everywhere_nonpos3121
