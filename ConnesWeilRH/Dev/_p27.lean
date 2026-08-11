import ConnesWeilRH.Dev.Wall14PlateauProbe
open MeasureTheory
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

lemma plateauAffine_hasCompactSupport (y : ℝ) :
    HasCompactSupport (fun t : ℝ => plateauReal (y - t)) := by
  let B : Set ℝ := Metric.closedBall (0 : ℝ) 1
  have hB : tsupport plateauReal = B := by
    have ht : tsupport ↑plateauBump = Metric.closedBall (0 : ℝ) 1 := ContDiffBump.tsupport_eq plateauBump
    simpa [plateauReal, B] using ht
  let pre : Set ℝ := (fun t : ℝ => y - t) ⁻¹' B
  have hcont : Continuous (fun t : ℝ => y - t) := continuous_const.sub continuous_id
  have hpre_closed : IsClosed pre := IsClosed.preimage hcont Metric.isClosed_closedBall
  have hsupp_comp : IsCompact pre := by
    have heq : pre = Metric.closedBall y 1 := by
      ext t; simp [B, pre, Metric.mem_closedBall, dist_eq_norm, abs_sub_comm]
    rw [heq]; exact isCompact_closedBall y 1
  have hsub : Function.support (fun t : ℝ => plateauReal (y - t)) ⊆ pre := by
    intro t ht
    have hyst : y - t ∈ tsupport plateauReal := subset_tsupport _ (by simpa [Function.mem_support] using ht)
    rwa [hB] at hyst
  have hsubcl : closure (Function.support (fun t : ℝ => plateauReal (y - t))) ⊆ pre :=
    (closure_mono hsub).trans (IsClosed.closure_subset hpre_closed)
  change IsCompact (tsupport (fun t : ℝ => plateauReal (y - t)))
  exact IsCompact.of_isClosed_subset hsupp_comp isClosed_closure hsubcl

lemma plateauSqRefl_integrable (y : ℝ) : Integrable (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (plateauReal (y - t)) ^ 2) :=
    (plateauReal_continuous.comp (continuous_const.sub continuous_id)).pow 2
  have hmul : HasCompactSupport (fun t : ℝ => plateauReal (y - t) * plateauReal (y - t)) :=
    HasCompactSupport.mul_right (plateauAffine_hasCompactSupport y)
  have hsc : HasCompactSupport (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hsc

theorem plateauA_eq_integral_realSq :
    plateauA = ∫ t : ℝ, (plateauReal t) ^ 2 := by
  rw [plateauA_eq_integral_normSq]
  congr 1; funext t
  have ht : plateauTest.test t = (plateauReal t : ℂ) := plateauTest_value_eq_ofReal t
  rw [ht]
  change Complex.normSq (plateauReal t) = (plateauReal t) ^ 2
  simp [Complex.normSq]; ring

theorem plateauF_le_A (y : ℝ) : plateauF y ≤ plateauA := by
  rw [plateauF_eq_conv, plateauA_eq_integral_realSq]
  let q : ℝ → ℝ := fun t => plateauReal (y - t)
  have hA1 : Integrable (fun t : ℝ => (plateauReal t) ^ 2) := plateauSq_integrable
  have hA2 : Integrable (fun s : ℝ => (q s) ^ 2) := by simpa [q] using plateauSqRefl_integrable y
  have hsm : Integrable (fun t : ℝ => (plateauReal t) ^ 2 + (q t) ^ 2) := hA1.add hA2
  have hg : Integrable (fun t : ℝ => (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2)) := by
    simpa [mul_comm] using hsm.const_mul (1/2 : ℝ)
  have h1 : Integrable (fun t : ℝ => plateauReal t * q t) := by simpa [q] using plateauRealMul_integrable y
  have hopw : ∀ t : ℝ, plateauReal t * q t ≤ (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2) := by
    intro t; nlinarith [sq_nonneg (plateauReal t - q t)]
  have hmono : (∫ t : ℝ, plateauReal t * q t) ≤ (∫ t : ℝ, (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2)) :=
    MeasureTheory.integral_mono h1 hg hopw
  have hreflect : (∫ t : ℝ, (q t) ^ 2) = ∫ t : ℝ, (plateauReal t) ^ 2 := by
    simpa [q] using integral_reflect_full_cont plateauRealSq_continuous y
  have hsum : (∫ t : ℝ, (plateauReal t) ^ 2 + (q t) ^ 2) =
      (∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2) := MeasureTheory.integral_add hA1 hA2
  have hlin : ∫ t : ℝ, (1/2 : ℝ) * ((plateauReal t) ^ 2 + (q t) ^ 2) =
      (1/2 : ℝ) * ((∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul (1/2 : ℝ) (fun t => (plateauReal t) ^ 2 + (q t) ^ 2)]
    rw [hsum]
  have hcollapse : (1/2 : ℝ) * ((∫ t : ℝ, (plateauReal t) ^ 2) + (∫ t : ℝ, (q t) ^ 2)) =
      ∫ t : ℝ, (plateauReal t) ^ 2 := by
    rw [hreflect]
    ring
  exact hmono.trans_eq (hlin.trans hcollapse)

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH

#print axioms ConnesWeilRH.Source.Dev.Wall14Plateau.plateauF_le_A
#print axioms ConnesWeilRH.Source.Dev.Wall14Plateau.plateauSqRefl_integrable
#print axioms ConnesWeilRH.Source.Dev.Wall14Plateau.plateauAffine_hasCompactSupport

