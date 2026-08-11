import ConnesWeilRH.Dev.Wall14PlateauProbe
open MeasureTheory
open scoped ComplexConjugate
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

-- negation invariance
lemma integral_neg_full_cont {f : ℝ → ℝ} (hfc : Continuous f) :
    (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
  let φ : ℝ → ℝ := fun t : ℝ => -t
  have hφ : AEMeasurable φ (volume : Measure ℝ) := measurable_neg.aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) := by
    simp [φ, Measure.map_neg_eq_self]
  have hfm : AEStronglyMeasurable f ((volume : Measure ℝ).map φ) := by
    rw [hmap]; exact hfc.aestronglyMeasurable
  have h := MeasureTheory.integral_map hφ (f := f) hfm
  simpa [φ] using h.symm.trans (by rw [hmap])

-- translation invariance
lemma integral_add_full_m {f : ℝ → ℝ} (hfc : Continuous f) (c : ℝ) :
    (∫ t : ℝ, f (t + c)) = ∫ t : ℝ, f t := by
  let φ : ℝ → ℝ 0 fun t : ℝ => t + c
  have hmeas : AEMeasurable φ (volume : Measure ℝ) :=
    (continuous_id.add continuous_const).aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) :=
    MeasureTheory.map_add_right_eq_self volume c
  have hfm : AEStronglyMeasurable f ((volume : Measure ℝ).map φ) := by
    rw [hmap]; exact hfc.aestronglyMeasurable
  have h := MeasureTheory.integral_map hmeas (f := f) hfm
  simpa [φ] using h.symm.trans (by rw [hmap])

-- reflect invariance
lemma integral_reflect (f : ℝ → ℝ) (hfc : Continuous f) (y : ℝ) :
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, f t := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hgc : Continuous g := hfc.comp continuous_neg
  have htr : (∫ t : ℝ, g (t + (-y))) = ∫ t : ℝ, g t := integral_add_full (hfc := hgc) (-y)
  have htg : (∫ t : ℝ, g (t - y)) = ∫ t : ℝ, g t := by
    simpa [sub_eq_add_neg] using htr
  have hneg : (∫ u : ℝ, g u) = ∫ t : ℝ, f t := integral_neg (hfc := h)
  calc
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, g (t - y) := by simp [g]
    _ = ∫ t : ℝ, g t := htg
    _ = ∫ t : ℝ, f t := hneg

-- reflected square integrable
lemma plateauSqRefl_integrable (y : ℝ) :
    Integrable (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (plateauReal (y - t)) ^ 2) :=
    (plateauReal_continuous.comp (continuous_const.sub continuous_id)).pow 2
  have hmul : HasCompactSupport (fun t : ℝ => plateauReal (y - t) * plateauReal (y - t)) :=
    HasCompactSupport.mul_right (plateauAff : _)
  have hsc : HasCompactSupport (fun t : ℝ => (plateauReal (y - t)) ^ 2) := by
    simpa [pow_two] using hmul
  exact hcont.integrable_of_hasCompactSupport hdata

-- plateauF_le_A the final bound
theorem plateauF_le_A (y : ℝ) : plateauF y ≤ plateauA := by
  rw [plateauF_eq_conv, plateauA_eq_integral_real]
  rfl
