import ConnesWeilRH.Dev.C1XiCenterTwoGammaPrefixTailConsumer

/-!
# C1XiCenterTwoGammaMassRelativeTail - mass-normalized tail consumer

The analytic tail estimate is strongest when its profile constant is supplied
by the same owner as the finite prefix.  This module specializes that
interface to a convolution square.  It does not manufacture the missing
mass-relative pointwise estimate: that estimate remains an explicit premise.
The value of the module is that, once such a certificate is proved, the tail
budget is expressed in the square mass rather than an opaque existential `L`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaMassRelativeTail

open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaSummedKernel
open C1XiCenterTwoGammaTailEstimate
open C1XiCenterTwoGammaPrefixTailConsumer
open CCM25Concrete.CompactLogConvolution
open MeasureTheory

noncomputable section

/-- The explicit tail budget when the local profile constant is `C` times the
convolution-square mass. -/
noncomputable def gammaRArchProfileTailMassRate
    (g : CompactLogTest) (C : Real) (N : Nat) : Real :=
  C * (g.convolutionSquare.test 0).re / (2 * (N : Real)) +
    2 * (g.convolutionSquare.test 0).re *
      Real.exp (-((2 * (N : Real) + 1) *
        (supportRadius g.convolutionSquare + 1))) *
      (1 - Real.exp (-(2 * (supportRadius g.convolutionSquare + 1))))⁻¹

/-- The zero value of a convolution square is a nonnegative real, so its
complex norm is exactly its real part. -/
theorem convolutionSquare_zero_norm_eq_re (g : CompactLogTest) :
    ‖g.convolutionSquare.test 0‖ =
      (g.convolutionSquare.test 0).re := by
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  exact abs_of_nonneg (integral_nonneg fun t =>
    Complex.normSq_nonneg (g.test t))

/-- A mass-scaled pointwise head certificate gives an explicit mass-scaled
absolute tail rate.  The support-tail premise is inherited from the general
profile owner; the head premise is the substantive analytic input. -/
theorem gammaRArchProfileTailNorm_le_mass_scaled_rate
    (g : CompactLogTest) (C : Real) (hC : 0 ≤ C)
    (hhead :
      ∀ (n : Nat) {y : Real},
        0 < y → y ≤ supportRadius g.convolutionSquare + 1 →
          ‖gammaRArchProfileTerm g.convolutionSquare n y‖ ≤
            C * (g.convolutionSquare.test 0).re * y *
              Real.exp (-(2 * (n : Real) * y)))
    (N : Nat) (hN : 0 < N) :
    gammaRArchProfileTailNorm g.convolutionSquare N ≤
      gammaRArchProfileTailMassRate g C N := by
  have hmass : 0 ≤ (g.convolutionSquare.test 0).re :=
    g.convolutionSquare_zero_re_nonnegative
  have hL : 0 ≤ C * (g.convolutionSquare.test 0).re :=
    mul_nonneg hC hmass
  obtain ⟨_L, _hL, _hhead, htail⟩ :=
    exists_gammaRArchProfile_pointwise_majorant g.convolutionSquare
  have hrate :=
    gammaRArchProfileTailNorm_le_explicit_rate_of_pointwise_majorant
      g.convolutionSquare (C * (g.convolutionSquare.test 0).re) hL hhead htail
      N hN
  unfold gammaRArchProfileTailExplicitRate at hrate
  rw [convolutionSquare_zero_norm_eq_re g] at hrate
  simpa [gammaRArchProfileTailMassRate] using hrate

/-- The prefix/tail consumer assembled with a mass-scaled tail certificate. -/
theorem archimedeanTerm_nonpos_of_mass_scaled_prefix_bound
    (g : CompactLogTest) (C : Real) (N : Nat) (hC : 0 ≤ C)
    (hN : 0 < N)
    (hhead :
      ∀ (n : Nat) {y : Real},
        0 < y → y ≤ supportRadius g.convolutionSquare + 1 →
          ‖gammaRArchProfileTerm g.convolutionSquare n y‖ ≤
            C * (g.convolutionSquare.test 0).re * y *
              Real.exp (-(2 * (n : Real) * y)))
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          g.convolutionSquare.test 0).re) +
        (∑ n ∈ Finset.range N,
          gammaRArchProfileIntegral g.convolutionSquare n).re ≤
          -gammaRArchProfileTailMassRate g C N) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0 := by
  apply archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound
    g.convolutionSquare N (gammaRArchProfileTailMassRate g C N) hprefix
  exact gammaRArchProfileTailNorm_le_mass_scaled_rate g C hC hhead N hN

/-- Strict version of the mass-scaled prefix/tail assembly. -/
theorem archimedeanTerm_neg_of_mass_scaled_prefix_bound
    (g : CompactLogTest) (C : Real) (N : Nat) (delta : Real)
    (hC : 0 ≤ C) (hN : 0 < N) (hdelta : 0 < delta)
    (hhead :
      ∀ (n : Nat) {y : Real},
        0 < y → y ≤ supportRadius g.convolutionSquare + 1 →
          ‖gammaRArchProfileTerm g.convolutionSquare n y‖ ≤
            C * (g.convolutionSquare.test 0).re * y *
              Real.exp (-(2 * (n : Real) * y)))
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          g.convolutionSquare.test 0).re) +
        (∑ n ∈ Finset.range N,
          gammaRArchProfileIntegral g.convolutionSquare n).re ≤
          -(gammaRArchProfileTailMassRate g C N + delta)) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare < 0 := by
  apply archimedeanTerm_neg_of_profilePrefix_bound_and_tailNorm_bound
    g.convolutionSquare N (gammaRArchProfileTailMassRate g C N) delta hdelta
    hprefix
  exact gammaRArchProfileTailNorm_le_mass_scaled_rate g C hC hhead N
    hN

end
end C1XiCenterTwoGammaMassRelativeTail
end Source
end ConnesWeilRH
