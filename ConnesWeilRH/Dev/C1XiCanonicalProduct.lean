import ConnesWeilRH.Dev.C1XiGlobalWeightedZeroSum
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# C1XiCanonicalProduct - genus-one xi factors

The global canonical-product comparison is still open.  This module fixes the
individual factor so its logarithmic derivative agrees exactly with the
existing multiplicity-weighted regularized zero term.  Later local-uniform
product work must retain this factor and its source-zero owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCanonicalProduct

open CC20ZetaCounting
open CC20YoshidaNearZeros
open C1XiGlobalZeroSum
open C1XiGlobalWeightedZeroSum
open C1SpectralWeil

noncomputable section

/-- The genus-one factor attached to one source-indexed xi zero, before its
analytic multiplicity is applied. -/
noncomputable def xiGenusOneAtom (rho : sourceNontrivialZeroSet)
    (s : Complex) : Complex :=
  (1 - s / rho.1) * Complex.exp (s / rho.1)

/-- The genus-one factor with the exact analytic multiplicity of its xi zero. -/
noncomputable def xiGenusOneFactor (rho : sourceNontrivialZeroSet)
    (s : Complex) : Complex :=
  xiGenusOneAtom rho s ^ xiMultiplicity rho

theorem sourceNontrivialZero_ne_zero (rho : sourceNontrivialZeroSet) :
    rho.1 ≠ 0 := by
  intro hzero
  have hre := sourceNontrivialZero_zero_lt_re rho.2
  rw [hzero] at hre
  norm_num at hre

theorem xiGenusOneAtom_ne_zero {rho : sourceNontrivialZeroSet} {s : Complex}
    (hs : s ≠ rho.1) : xiGenusOneAtom rho s ≠ 0 := by
  have hrho : rho.1 ≠ 0 := sourceNontrivialZero_ne_zero rho
  unfold xiGenusOneAtom
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    apply hs
    have hratio : s / rho.1 = 1 := h.symm
    have hmul : s = 1 * rho.1 := (div_eq_iff hrho).mp hratio
    simpa using hmul
  · exact Complex.exp_ne_zero _

theorem differentiableAt_xiGenusOneAtom (rho : sourceNontrivialZeroSet)
    (s : Complex) : DifferentiableAt Complex (xiGenusOneAtom rho) s := by
  unfold xiGenusOneAtom
  fun_prop

theorem logDeriv_xiGenusOneAtom_eq_regularizedZeroTerm
    (rho : sourceNontrivialZeroSet) {s : Complex} (hs : s ≠ rho.1) :
    logDeriv (xiGenusOneAtom rho) s = regularizedZeroTerm s rho := by
  have hrho : rho.1 ≠ 0 := sourceNontrivialZero_ne_zero rho
  have hdiv : HasDerivAt (fun z : Complex => z / rho.1) (1 / rho.1) s := by
    simpa using (hasDerivAt_id' (x := s)).div_const rho.1
  have hleft : HasDerivAt (fun z : Complex => 1 - z / rho.1) (-(1 / rho.1)) s := by
    simpa using (hasDerivAt_const s (1 : Complex)).sub hdiv
  have hright : HasDerivAt (fun z : Complex => Complex.exp (z / rho.1))
      (Complex.exp (s / rho.1) * (1 / rho.1)) s := by
    simpa using hdiv.cexp
  have hatom : HasDerivAt (xiGenusOneAtom rho)
      ((-(1 / rho.1)) * Complex.exp (s / rho.1) +
        (1 - s / rho.1) * (Complex.exp (s / rho.1) * (1 / rho.1))) s := by
    simpa only [xiGenusOneAtom] using hleft.mul hright
  have hlinear : 1 - s / rho.1 ≠ 0 := by
    intro hzero
    apply hs
    have hratio : s / rho.1 = 1 := (sub_eq_zero.mp hzero).symm
    have hmul : s = 1 * rho.1 := (div_eq_iff hrho).mp hratio
    simpa using hmul
  rw [logDeriv_apply, hatom.deriv]
  unfold xiGenusOneAtom regularizedZeroTerm
  have hs_sub_rho : s - rho.1 ≠ 0 := sub_ne_zero.mpr hs
  have hrho_sub_s : rho.1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  have hneg_rho_add_s : -rho.1 + s ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hs_sub_rho
  field_simp [hrho, hlinear, hs_sub_rho, hrho_sub_s, hneg_rho_add_s,
    Complex.exp_ne_zero]
  ring

theorem differentiableAt_xiGenusOneFactor (rho : sourceNontrivialZeroSet)
    (s : Complex) : DifferentiableAt Complex (xiGenusOneFactor rho) s := by
  unfold xiGenusOneFactor
  exact (differentiableAt_xiGenusOneAtom rho s).pow _

theorem logDeriv_xiGenusOneFactor_eq_weightedRegularizedZeroTerm
    (rho : sourceNontrivialZeroSet) {s : Complex} (hs : s ≠ rho.1) :
    logDeriv (xiGenusOneFactor rho) s = weightedRegularizedZeroTerm s rho := by
  unfold xiGenusOneFactor
  rw [logDeriv_fun_pow (differentiableAt_xiGenusOneAtom rho s),
    logDeriv_xiGenusOneAtom_eq_regularizedZeroTerm rho hs]
  unfold weightedRegularizedZeroTerm
  norm_num

end
end C1XiCanonicalProduct
end Source
end ConnesWeilRH
