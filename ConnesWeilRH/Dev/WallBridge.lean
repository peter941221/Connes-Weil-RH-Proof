import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Bridge

open MeasureTheory
open scoped Topology
open Filter Set
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.Dev.Wall14Plateau
open scoped ComplexConjugate

noncomputable def convBump : CompactLogTest :=
  bumpPlateauTest.convolution bumpPlateauTest

theorem convBump_zero : convBump.test 0 = (bumpA : Complex) := by
  unfold convBump
  rw [CompactLogTest.convolution_apply]
  have hL : (∫ t : ℝ, bumpPlateauTest.test t * bumpPlateauTest.test (0 - t)) =
        ∫ t : ℝ, (Complex.normSq (bumpPlateauTest.test t) : Complex) := by
    apply integral_congr_ae
    filter_upwards with t
    have hstar0 : star (bumpPlateauTest.test (-t)) = bumpPlateauTest.test t := by
      simpa [CompactLogTest.involution_apply] using (bumpPlateauInvolution_real_even t)
    have hsub : bumpPlateauTest.test (0 - t) = bumpPlateauTest.test (-t) := by
      congr 1 <;> ring
    have hstar : bumpPlateauTest.test (-t) = star (bumpPlateauTest.test t) := by
      simpa [star_star] using (congrArg star hstar0)
    calc
      bumpPlateauTest.test t * bumpPlateauTest.test (0 - t)
          = bumpPlateauTest.test t * star (bumpPlateauTest.test t) := by
            rw [hsub, hstar]
      _ = Complex.normSq (bumpPlateauTest.test t) := by
            rw [mul_comm, Complex.normSq_eq_conj_mul_self]
            simp [Complex.star_def]
  rw [hL]
  rw [bumpA_eq_integral_normSq]
  rw [integral_complex_ofReal]


/-- `convBump` is nonzero at 0 (value `bumpA > 0`). -/
theorem convBump_test0_ne_zero : convBump.test 0 ≠ 0 := by
  rw [convBump_zero]
  exact_mod_cast (ne_of_gt bumpA_pos)

/-- `normSq(convBump)` is integrable (compact support + continuous). -/
theorem convBump_normSq_integrable :
    Integrable (fun x : ℝ => Complex.normSq (convBump.test x)) := by
  have hcont : Continuous (fun x : ℝ => Complex.normSq (convBump.test x)) := by
    fun_prop
  have hcomp : HasCompactSupport (fun x : ℝ => Complex.normSq (convBump.test x)) := by
    exact convBump.compactSupport.comp_left (map_zero _)
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- The L2 norm-square of `convBump` is strictly positive. -/
theorem convBump_normSq_integral_pos :
    0 < ∫ x : ℝ, Complex.normSq (convBump.test x) := by
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (f_cont := by fun_prop)
    (f_int := convBump_normSq_integrable)
    (f_nonneg := fun x => Complex.normSq_nonneg (convBump.test x))
    (f_x := by
      dsimp
      rw [Complex.normSq_eq_zero]
      exact convBump_test0_ne_zero)

/-- The 4-fold owner's leading term (convolution-square at 0, real part) is positive. -/
theorem convBump_square0_re_pos :
    0 < (convBump.convolutionSquare.test 0).re := by
  rw [convBump.convolutionSquare_zero_eq_integral_normSq]
  simpa using convBump_normSq_integral_pos

end Wall14Bridge
end Dev
end Source
end ConnesWeilRH
