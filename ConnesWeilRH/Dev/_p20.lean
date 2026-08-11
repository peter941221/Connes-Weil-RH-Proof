import ConnesWeilRH.Dev.Wall14PlateauProbe
open MeasureTheory
open scoped ComplexConjugate
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

-- full-real negation invariance (continuous integrand)
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

-- full-real translation invariance (continuous integrand)
lemma integral_add_full_cont {f : ℝ → ℝ} (hfc : Continuous f) (c : ℝ) :
    (∫ t : ℝ, f (t + c)) = ∫ t : ℝ, f t := by
  let φ : ℝ → ℝ := fun t : ℝ => t + c
  have hmeas : AEMeasurable φ (volume : Measure ℝ) :=
    (continuous_id.add continuous_const).aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) :=
    MeasureTheory.map_add_right_eq_self (volume : Measure ℝ) c
  have hfm : AEStronglyMeasurable f ((volume : Measure ℝ).map φ) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have h := MeasureTheory.integral_map hmeas (f := f) hfm
  simpa [φ] using h.symm.trans (by rw [hmap])

-- full-real reflection invariance: ∫ f (y - t) = ∫ f
lemma integral_reflect_full_cont {f : ℝ → ℝ} (hfc : Continuous f) (y : ℝ) :
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, f t := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hgc : Continuous g := hfc.comp continuous_neg
  have htrans : (∫ t : ℝ, g (t + (-y))) = ∫ t : ℝ, g t := integral_add_full_cont hgc (-y)
  have hneg : (∫ u : ℝ, g u) = ∫ t : ℝ, f t := integral_neg_full_cont hfc
  have htg : (∫ t : ℝ, g (t - y)) = ∫ t : ℝ, g t := by
    simpa [sub_eq_add_neg] using htrans
  calc
    (∫ t : ℝ, f (y - t)) = ∫ t : ℝ, g (t - y) := by
      congr; funext t; simp [g]
    _ = ∫ t : ℝ, g t := htg
    _ = ∫ t : ℝ, f t := hneg

-- continuous square
lemma plateauRealSq_continuous : Continuous (fun t : ℝ => (plateauReal t) ^ 2) := by
  exact plateauReal_continuous.pow 2

-- (p t)^2 integrable
lemma plateauSq_integrable : Integrable (fun t : ℝ => (plateauReal t) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => (plateauReal t) ^ 2) := plateauRealSq_continuous
  have hp : HasCompactSupport (fun t : ℝ => plateauReal t) := ContDiffBump.hasCompactSupport plateauBump
  have hcomp : HasCompactSupport (fun t : ℝ => (plateauReal t) ^ 2) := by
    simpa [pow_two] using (HasCompactSupport.mul_right hp : HasCompactSupport (fun t : ℝ => plateauReal t * plateauReal t))
  exact hcont.integrable_of_hasCompactSupport hcomp

-- support of plateau affine is compact (support = ball c..)
lemma plateauAffine_hasCompactSupport (y : ℝ) :
    HasCompactSupport (fun t : ℝ => plateauReal (y - t)) := by
  -- support of t ↦ p(y-t) lies in closedBall y 1, compact
  let B : Set ℝ := Metric.closedBall (0 : ℝ) 1
  have hts : tsupport ↑plateauBump = B := ContDiffBump.tsupport_eq plateauBump
  have hsup : Function.support plateauReal ⊆ B := by
    intro x hx
    have hx' : x ∈ tsupport ↑plateauBump := by
      apply subset_tsupport
      exact hx
    simpa [plateauReal] using (by simpa [hts] using hx')
  have hpre : Function.support (fun t : ℝ => plateauReal (y - t)) ⊆
      (fun t : ℝ => y - t) ⁻¹' B := fun t ht => hsup (by simpa using ht)
  -- preimage of closedBall under affine is closedBall y 1, compact
  have hbounded_pre : (fun t : ℝ => y - t) ⁻¹' (closedBall (0:ℝ) 1) = closedBall y 1 := by
    ext t; simp [dist_eq_norm, sub_eq_add_neg, abs_neg]
  have hc : IsCompact ((fun t : ℝ => y - t) ⁻¹' (closedBall (0:ℝ) 1)) := by
    rw [hbounded_pre]; exact isCompact_closedBall
  -- HasCompactSupport: closure(incl) compact because subset of comp set
  exact IsCompact.of_isClosed_subset hcmp hc (isClosed_closure.subset hsup...) 2

end
