import ConnesWeilRH.Dev.Wall14PlateauProbe
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula

/-!
# Wall14PlateauIntegral

Bounds the real part of the archimedean integral at the plateau owner.  This
file proves the plateau foundations, the Re-identity, and the tail (y>2) bound.
RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set
open scoped ComplexConjugate
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner

theorem plateauReal_eq_zero_of_abs_ge (t : ℝ) (ht : (1 : ℝ) ≤ |t|) : plateauReal t = 0 := by
  apply plateauBump.zero_of_le_dist
  have hdist : dist t 0 = |t| := by rw [dist_eq_norm]; simp
  rwa [hdist]

theorem plateauReal_ne_zero_imp_abs_lt_one (t : ℝ) (ht : plateauReal t ≠ 0) : |t| < 1 := by
  by_contra h
  have hn : (1 : ℝ) ≤ |t| := le_of_not_gt h
  have hz : plateauReal t = 0 := plateauReal_eq_zero_of_abs_ge t hn
  exact ht hz

theorem plateauF_symm (y : ℝ) : plateauF (-y) = plateauF y := by
  let f : ℝ → ℝ := fun t => plateauReal t * plateauReal (y + t)
  have hfc : Continuous f :=
    plateauReal_continuous.mul
      (plateauReal_continuous.comp (by fun_prop : Continuous (fun t : ℝ => y + t)))
  have him : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := integral_neg_full_cont (f := f) hfc
  have heq : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, plateauReal t * plateauReal (y - t) := by
    congr 1; funext t
    simp [f]
    have : y + (-t) = y - t := by ring
    rw [this, plateauReal_neg]
  have hcross : (∫ t : ℝ, plateauReal t * plateauReal (y - t))
        = ∫ t : ℝ, plateauReal t * plateauReal (y + t) := (heq.symm.trans him)
  have hrepL : (∫ t : ℝ, plateauReal t * plateauReal ((-y) - t))
        = ∫ t : ℝ, plateauReal t * plateauReal (y + t) := by
    congr 1; funext t
    have hseg : (-y) - t = -(y + t) := by ring
    rw [hseg, plateauReal_neg]
  calc
    plateauF (-y) = ∫ t : ℝ, plateauReal t * plateauReal ((-y) - t) := by rw [plateauF_eq_conv]
    _ = ∫ t : ℝ, plateauReal t * plateauReal (y + t) := hrepL
    _ = ∫ t : ℝ, plateauReal t * plateauReal (y - t) := hcross.symm
    _ = plateauF y := by rw [plateauF_eq_conv]

theorem plateauF_eq_zero_of_two_le_abs (y : ℝ) (hy : (2 : ℝ) ≤ |y|) : plateauF y = 0 := by
  have hzero : (fun t : ℝ => plateauReal t * plateauReal (y - t)) = fun _ : ℝ => 0 := by
    funext t
    by_cases hp1 : plateauReal t = 0
    · simp [hp1]
    · have ht1 : |t| < 1 := plateauReal_ne_zero_imp_abs_lt_one t hp1
      by_cases hp2 : |y - t| ≥ (1 : ℝ)
      · have ha : plateauReal (y - t) = 0 := plateauReal_eq_zero_of_abs_ge (y - t) hp2
        simp [ha]
      · have hy1 : |y - t| < 1 := lt_of_not_ge hp2
        have htri : |y| ≤ |t| + |y - t| := by
          rw [add_comm]
          exact (show |y| = |(y - t) + t| by congr 1; ring).trans_le (abs_add_le (y - t) t)
        have : |y| < (2 : ℝ) := by nlinarith
        have : (2 : ℝ) ≤ |y| := hy
        exfalso; linarith
  rw [plateauF_eq_conv]
  rw [hzero]
  simp

/-! Re(archimedeanNumerator y) = 2*(e^{y/2} * F(y) - A). -/
lemma archimedeanNumeratorRe_eq_two_G (y : ℝ) :
    plateauOwner.archimedeanNumeratorRe y = 2 * (Real.exp (y / 2) * plateauF y - plateauA) := by
  unfold archimedeanNumeratorRe archimedeanNumerator
  rw [plateauOwner.convolutionSquare_add_neg_eq_two_re]
  change ((Real.exp (y / 2) : ℂ) * ((2 * plateauF y : ℝ) : ℂ) - (2 : ℂ) * plateauOwner.convolutionSquare.test 0).re
    = 2 * (Real.exp (y / 2) * plateauF y - plateauA)
  have h1 : ((Real.exp (y / 2) : ℂ) * ((2 * plateauF y : ℝ) : ℂ)).re
      = Real.exp (y / 2) * (2 * plateauF y) := by
    rw [Complex.re_ofReal_mul]; simp
  have h2 : ((2 : ℂ) * plateauOwner.convolutionSquare.test 0).re = 2 * plateauA := by
    simpa [plateauA] using (Complex.re_ofReal_mul (2 : ℝ) (plateauOwner.convolutionSquare.test 0))
  rw [Complex.sub_re]
  rw [h1, h2]
  ring

/-! The real archimedean density. -/
noncomputable def plateauArchG (y : ℝ) : ℝ :=
  2 * (Real.exp (y / 2) * plateauF y - plateauA) / den y

/-! Re(integrand y) = plateauArchG y for y>0 (denominator nonzero). -/
lemma archimedeanIntegrand_re_eq_plateauArchG (y : ℝ) (hy : 0 < y) :
    (plateauOwner.archimedeanIntegrand y).re = plateauArchG y := by
  unfold plateauArchG archimedeanIntegrand
  rw [archimedeanNumeratorRe_eq_two_G]
  have hd0 : (den y : ℂ) ≠ 0 := by exact_mod_cast (den_pos y hy).ne'
  have hdim : (plateauOwner.archimedeanNumerator y).im = 0 :=
    plateauOwner.archimedeanNumerator_im_eq_zero
  -- Re( num / (den:ℂ) ) = num.re / den
  have hdiv : (plateauOwner.archimedeanNumerator y / (den y : ℂ)).re
      = plateauOwner.archimedeanNumeratorRe y / den y := by
    rw [Complex.div_re]
    have hd : (den y : ℂ).im = 0 := by
      change (((den y) : ℝ) : ℂ).im = 0
      simp
    rw [hdim, hd]
    field_simp [Complex.normSq]
  rw [archimedeanDeNominator, den]  -- structural
  rw [show archimedeanDenominator y = den y by rfl]
  simpa [archimedeanNumeratorRe] using h
end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
