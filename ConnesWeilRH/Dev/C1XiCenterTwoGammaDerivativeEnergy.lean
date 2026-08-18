import ConnesWeilRH.Dev.C1XiCenterTwoGammaMassRelativeTail
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# C1XiCenterTwoGammaDerivativeEnergy

The shifted Gamma_R tail needs a support-local Lipschitz certificate for a
convolution square.  A mass-only certificate is not frequency-uniform, so this
file records the derivative-energy producer instead.  Cauchy--Schwarz bounds
the derivative of `g* * g` by the product of the `L2` mass of `g` and the `L2`
energy of `g'`.

This is an analytic producer only.  It does not prove the finite constrained
prefix inequality, global spectral nonnegativity, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaDerivativeEnergy

open MeasureTheory
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaSummedKernel
open C1XiCenterTwoGammaTailEstimate
open C1XiCenterTwoGammaMassRelativeTail
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactLogConvolution.CompactLogTest
open scoped ContDiff Convolution

noncomputable section

/-- The squared `L2` energy of the compact-log derivative. -/
noncomputable def compactLogDerivativeEnergy (g : CompactLogTest) : Real :=
  ∫ t : Real, ‖deriv (g.test : Real → Complex) t‖ ^ (2 : Real)

/-- The homogeneous derivative-energy coefficient for a convolution square. -/
noncomputable def convolutionSquareDerivativeEnergyCoefficient
    (g : CompactLogTest) : Real :=
  Real.sqrt ((g.convolutionSquare.test 0).re) *
    Real.sqrt (compactLogDerivativeEnergy g)

private theorem derivative_memLp_two (g : CompactLogTest) :
    MemLp (deriv (g.test : Real → Complex)) (ENNReal.ofReal (2 : Real)) := by
  have hcont : Continuous (deriv (g.test : Real → Complex)) :=
    (g.test.smooth 1).continuous_deriv le_rfl
  exact hcont.memLp_of_hasCompactSupport g.compactSupport.deriv

private theorem derivative_energy_nonnegative (g : CompactLogTest) :
    0 ≤ compactLogDerivativeEnergy g := by
  unfold compactLogDerivativeEnergy
  exact integral_nonneg fun t => by positivity

private theorem involution_mass_integral (g : CompactLogTest) :
    (∫ t : Real, ‖g.involution.test t‖ ^ (2 : Real)) =
      ∫ t : Real, Complex.normSq (g.test t) := by
  have hneg : MeasurePreserving (fun t : Real => -t) volume volume :=
    Measure.measurePreserving_neg volume
  have hchange :
      (∫ t : Real, ‖g.test (-t)‖ ^ (2 : Real)) =
        ∫ t : Real, ‖g.test t‖ ^ (2 : Real) := by
    simpa only [Function.comp_apply] using
      hneg.integral_comp (Homeomorph.neg Real).measurableEmbedding
        (fun t : Real => ‖g.test t‖ ^ (2 : Real))
  rw [show (fun t : Real => ‖g.involution.test t‖ ^ (2 : Real)) =
      (fun t : Real => ‖g.test (-t)‖ ^ (2 : Real)) by
        funext t
        simp only [involution_apply, norm_star]]
  rw [hchange]
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

private theorem derivative_energy_translation (g : CompactLogTest) (x : Real) :
    (∫ t : Real, ‖deriv (g.test : Real → Complex) (x - t)‖ ^ (2 : Real)) =
      compactLogDerivativeEnergy g := by
  have hsub : MeasurePreserving (fun t : Real => x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure Real)).add_left volume x
  unfold compactLogDerivativeEnergy
  simpa only [Function.comp_apply] using
    hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding
      (fun t : Real => ‖deriv (g.test : Real → Complex) t‖ ^ (2 : Real))

private theorem convolutionSquare_deriv_hasDerivAt
    (g : CompactLogTest) (x : Real) :
    HasDerivAt (g.convolutionSquare.test)
      ((g.involution.test ⋆[ContinuousLinearMap.mul Real Complex, volume]
        deriv (g.test : Real → Complex)) x) x := by
  change HasDerivAt
    (fun z : Real =>
      (g.involution.test ⋆[ContinuousLinearMap.mul Real Complex, volume]
        g.test) z)
    ((g.involution.test ⋆[ContinuousLinearMap.mul Real Complex, volume]
      deriv (g.test : Real → Complex)) x) x
  exact g.compactSupport.hasDerivAt_convolution_right
    (ContinuousLinearMap.mul Real Complex)
    g.involution.test.integrable.locallyIntegrable
    (g.test.smooth 1) x

/-- Pointwise derivative bound for the genuine convolution square. -/
theorem norm_deriv_convolutionSquare_le_derivativeEnergyCoefficient
    (g : CompactLogTest) (x : Real) :
    ‖deriv (g.convolutionSquare.test) x‖ ≤
      convolutionSquareDerivativeEnergyCoefficient g := by
  have hderiv := convolutionSquare_deriv_hasDerivAt g x
  have hderiv_eq :
      deriv (g.convolutionSquare.test) x =
        ((g.involution.test ⋆[ContinuousLinearMap.mul Real Complex, volume]
          deriv (g.test : Real → Complex)) x) :=
    hderiv.deriv
  rw [hderiv_eq]
  rw [convolution_def]
  have hholder : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hleft : MemLp (g.involution.test : Real → Complex)
      (ENNReal.ofReal (2 : Real)) :=
    SchwartzMap.memLp g.involution.test (ENNReal.ofReal (2 : Real))
  have hrightBase := derivative_memLp_two g
  have hsub : MeasurePreserving (fun t : Real => x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure Real)).add_left volume x
  have hright : MemLp (fun t : Real => deriv (g.test : Real → Complex) (x - t))
      (ENNReal.ofReal (2 : Real)) := by
    simpa only [Function.comp_apply] using hrightBase.comp_measurePreserving hsub
  have hbound :
      ‖∫ t : Real, g.involution.test t * deriv (g.test : Real → Complex) (x - t)‖ ≤
        ∫ t : Real, ‖g.involution.test t *
          deriv (g.test : Real → Complex) (x - t)‖ :=
    norm_integral_le_integral_norm _
  have hholder_bound := integral_mul_norm_le_Lp_mul_Lq hholder hleft hright
  have hleft_norm_integral :
      (∫ t : Real, ‖g.involution.test t‖ ^ (2 : Real)) =
        ∫ t : Real, Complex.normSq (g.test t) :=
    involution_mass_integral g
  have hright_norm_integral :
      (∫ t : Real, ‖deriv (g.test : Real → Complex) (x - t)‖ ^ (2 : Real)) =
        compactLogDerivativeEnergy g :=
    derivative_energy_translation g x
  have hholder_bound' :
      (∫ t : Real, ‖g.involution.test t‖ *
        ‖deriv (g.test : Real → Complex) (x - t)‖) ≤
      (∫ t : Real, Complex.normSq (g.test t)) ^ (1 / (2 : Real)) *
        (compactLogDerivativeEnergy g) ^ (1 / (2 : Real)) := by
    have hraw :
        (∫ t : Real, ‖g.involution.test t‖ *
          ‖deriv (g.test : Real → Complex) (x - t)‖) ≤
          (∫ t : Real, ‖g.involution.test t‖ ^ (2 : Real)) ^
              (1 / (2 : Real)) *
            (∫ t : Real, ‖deriv (g.test : Real → Complex) (x - t)‖ ^
              (2 : Real)) ^ (1 / (2 : Real)) :=
      integral_mul_norm_le_Lp_mul_Lq hholder hleft hright
    rw [hleft_norm_integral, hright_norm_integral] at hraw
    exact hraw
  calc
    ‖∫ t : Real, g.involution.test t *
        deriv (g.test : Real → Complex) (x - t)‖ ≤
        ∫ t : Real, ‖g.involution.test t *
          deriv (g.test : Real → Complex) (x - t)‖ := hbound
    _ = ∫ t : Real, ‖g.involution.test t‖ *
        ‖deriv (g.test : Real → Complex) (x - t)‖ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_mul]
    _ ≤ (∫ t : Real, Complex.normSq (g.test t)) ^ (1 / (2 : Real)) *
        (compactLogDerivativeEnergy g) ^ (1 / (2 : Real)) := hholder_bound'
    _ = convolutionSquareDerivativeEnergyCoefficient g := by
      unfold convolutionSquareDerivativeEnergyCoefficient
      rw [g.convolutionSquare_zero_eq_integral_normSq]
      simp only [Complex.ofReal_re]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- The pointwise derivative producer becomes the support-local Lipschitz
certificate consumed by the Gamma_R profile estimate. -/
theorem convolutionSquare_support_lipschitz_of_derivative_energy
    (g : CompactLogTest) :
    ∀ x ∈ Set.Icc (-(supportRadius g.convolutionSquare + 1))
        (supportRadius g.convolutionSquare + 1),
      ∀ z ∈ Set.Icc (-(supportRadius g.convolutionSquare + 1))
        (supportRadius g.convolutionSquare + 1),
        ‖g.convolutionSquare.test x - g.convolutionSquare.test z‖ ≤
          convolutionSquareDerivativeEnergyCoefficient g * ‖x - z‖ := by
  intro x hx z hz
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := Real)
  · intro w _
    exact (convolutionSquare_deriv_hasDerivAt g w).differentiableAt
  · intro w _
    exact norm_deriv_convolutionSquare_le_derivativeEnergyCoefficient g w
  · exact convex_univ
  · exact Set.mem_univ z
  · exact Set.mem_univ x

/-- The explicit profile constant produced by the derivative-energy bound. -/
noncomputable def convolutionSquareDerivativeEnergyProfileConstant
    (g : CompactLogTest) : Real :=
  2 * convolutionSquareDerivativeEnergyCoefficient g +
    (g.convolutionSquare.test 0).re

private theorem convolutionSquareDerivativeEnergyProfileConstant_nonnegative
    (g : CompactLogTest) :
    0 ≤ convolutionSquareDerivativeEnergyProfileConstant g := by
  unfold convolutionSquareDerivativeEnergyProfileConstant
  have hmass : 0 ≤ (g.convolutionSquare.test 0).re :=
    g.convolutionSquare_zero_re_nonnegative
  have henergy : 0 ≤ compactLogDerivativeEnergy g :=
    derivative_energy_nonnegative g
  have hcoef : 0 ≤ convolutionSquareDerivativeEnergyCoefficient g := by
    unfold convolutionSquareDerivativeEnergyCoefficient
    positivity
  linarith

/-- The derivative-energy producer supplies the explicit shifted Gamma_R tail
rate.  This is a magnitude bound; it makes no sign claim about the tail. -/
theorem gammaRArchProfileTailNorm_le_derivativeEnergy_rate
    (g : CompactLogTest) (N : Nat) (hN : 0 < N) :
    gammaRArchProfileTailNorm g.convolutionSquare N ≤
      gammaRArchProfileTailExplicitRate g.convolutionSquare
        (convolutionSquareDerivativeEnergyProfileConstant g) N := by
  apply gammaRArchProfileTailNorm_le_explicit_rate_of_pointwise_majorant
    g.convolutionSquare
    (convolutionSquareDerivativeEnergyProfileConstant g)
    (convolutionSquareDerivativeEnergyProfileConstant_nonnegative g)
  · intro n y hy0 hyS
    have hterm :=
      gammaRArchProfileTerm_norm_le_of_support_lipschitz
        g.convolutionSquare (convolutionSquareDerivativeEnergyCoefficient g)
        (by
          unfold convolutionSquareDerivativeEnergyCoefficient
          have hm := g.convolutionSquare_zero_re_nonnegative
          have he := derivative_energy_nonnegative g
          positivity)
        (convolutionSquare_support_lipschitz_of_derivative_energy g)
        n hy0 hyS
    rw [convolutionSquare_zero_norm_eq_re g] at hterm
    simpa [convolutionSquareDerivativeEnergyProfileConstant] using hterm
  · intro n y hy
    obtain ⟨_, _, _, htail⟩ :=
      exists_gammaRArchProfile_pointwise_majorant g.convolutionSquare
    exact htail n hy
  · exact hN

end
end C1XiCenterTwoGammaDerivativeEnergy
end Source
end ConnesWeilRH
