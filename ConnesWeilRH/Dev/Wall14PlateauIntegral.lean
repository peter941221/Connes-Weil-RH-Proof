import ConnesWeilRH.Dev.Wall14PlateauProbe
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula

/-!
# Wall14PlateauIntegral

Foundation facts for the Wall-A 1.4 ``hI`` closure at the large-plateau owner:
plateau support radius 1, even ``F``, F=0 for |y|>=2, the formula
``Re(archimedeanNumerator y)=2(e^{y/2}F(y)-A)``, and the real part of the
archimedean integrand.  RH NOT claimed.
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

theorem plateauReal_eq_zero_of_abs_ge (t : ℝ) (ht : (1 : ℝ) ≤ |t|) :
    plateauReal t = 0 := by
  apply plateauBump.zero_of_le_dist
  have hdist : dist t 0 = |t| := by
    rw [dist_eq_norm]
    simp
  rwa [hdist]

theorem plateauReal_ne_zero_imp_abs_lt_one (t : ℝ) (ht : plateauReal t ≠ 0) :
    |t| < 1 := by
  by_contra h
  have hn : (1 : ℝ) ≤ |t| := le_of_not_gt h
  have hz : plateauReal t = 0 := plateauReal_eq_zero_of_abs_ge t hn
  exact ht hz

/-! F(-y)=F(y): the convolution square is even. -/
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

/-! F(y)=0 when |y| >= 2 (convolution support radius 2). -/
theorem plateauF_eq_zero_of_two_le_abs (y : ℝ) (hy : (2 : ℝ) ≤ |y|) :
    plateauF y = 0 := by
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
        have hy2 : |y| < (2 : ℝ) := by nlinarith
        have hc : (2 : ℝ) ≤ |y| := hy
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

/-! Real part of the archimedean integrand. -/
noncomputable def plateauArchG (y : ℝ) : ℝ :=
  plateauOwner.archimedeanNumeratorRe y / den y

/-! (Re(integrand y)) = plateauArchG y for y > 0. -/
lemma archimedeanIntegrand_re_eq_plateauArchG (y : ℝ) (hy : 0 < y) :
    (plateauOwner.archimedeanIntegrand y).re = plateauArchG y := by
  unfold plateauArchG archimedeanIntegrand
  have hd0 : (den y : ℂ) ≠ 0 := by exact_mod_cast (den_pos y hy).ne'
  have him : (plateauOwner.archimedeanNumerator y).im = 0 :=
    plateauOwner.archimedeanNumerator_im_eq_zero y
  have hden : archimedeanDenominator y = den y := by rfl
  rw [hden]
  rw [Complex.div_re]
  have hd : ((den y : ℂ)).im = 0 := by simp
  have hr : ((den y : ℂ)).re = den y := by simp
  have hnorm : Complex.normSq (den y : ℂ) = (den y) ^ 2 := by
    rw [Complex.normSq_apply]; rw [hr, hd]; ring
  rw [him, hr, hd, hnorm]
  field_simp [(den_pos y hy).ne', hr]
  unfold archimedeanNumeratorRe
  ring

/-! ### Pointwise bounds for the ``hI`` closure

``g y = plateauArchG y = 2(e^{y/2}F(y)-A)/den y`` with ``0<=F<=A`` and ``den>0``
on ``y>0``.  On the tail ``y>=2`` we have ``F=0``; on the middle band ``[1,2]``
we use the crude ``2A e^{y/2}/den``.  RH NOT claimed.
-/


/-- On the tail ``y>=2`` the real part is exactly ``-2A/den``, so its absolute
value is ``2A/den``, decaying like the exponential ``e^{-y}``. -/
lemma plateauG_abs_tail (y : ℝ) (hy : 2 ≤ y) :
    |plateauArchG y| = 2 * plateauA / den y := by
  unfold plateauArchG
  rw [archimedeanNumeratorRe_eq_two_G]
  have hy0 : 0 ≤ y := by linarith
  have hF : plateauF y = 0 :=
    plateauF_eq_zero_of_two_le_abs y (by simpa [abs_of_nonneg hy0])
  have hdp : 0 < den y := den_pos y (by linarith)
  rw [hF, show 2 * (Real.exp (y / 2) * 0 - plateauA) = -(2 * plateauA) by ring]
  rw [abs_div, abs_neg]
  have h2A : (0 : ℝ) ≤ 2 * plateauA := mul_nonneg (by norm_num) (le_of_lt plateauA_pos)
  have hdenAbs : |den y| = den y := abs_of_nonneg (le_of_lt hdp)
  rw [abs_of_nonneg h2A, hdenAbs]

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
