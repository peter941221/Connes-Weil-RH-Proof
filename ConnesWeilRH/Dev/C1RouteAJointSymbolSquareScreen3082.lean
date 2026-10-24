import ConnesWeilRH.Dev.C1RouteAJointSymbolData3080

/-!
# Route A Gate 1: single-prime square-kernel screen (record 3082)

The most direct square-kernel proposal would assign a nonnegative kernel to
each prime Poisson contribution separately.  This screen records the exact
algebraic obstruction: one prime contribution changes sign as the frequency
varies.  It therefore cannot itself be a pointwise nonnegative kernel.
This does not exclude a genuinely joint factorization involving all primes.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAJointSymbolSquareScreen3082

open C1RouteAJointSymbolData3080
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open C1HealthyYoshidaUnscaledOrbit
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner

noncomputable section

theorem routeAPrimePoissonSymbol_zero_frequency_pos
    (p : Nat) (hp : Nat.Prime p) :
    0 < routeAPrimePoissonSymbol p 0 := by
  let r : Real := 1 / Real.sqrt (p : Real)
  have hpcast : (1 : Real) < (p : Real) := by exact_mod_cast hp.one_lt
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (p : Real) by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (1 - Real.sqrt (p : Real))]
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (show 0 < (p : Real) by positivity))]
    simpa using hsqrt
  unfold routeAPrimePoissonSymbol
  dsimp [r]
  simp only [mul_zero, Real.cos_zero]
  change (1 - r ^ 2) / (1 - 2 * r * 1 + r ^ 2) - 1 > 0
  have hd : 0 < 1 - 2 * r * 1 + r ^ 2 := by
    nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  apply sub_pos.mpr
  apply (lt_div_iff₀ hd).2
  nlinarith [hrpos, hrlt]

theorem routeAPrimePoissonSymbol_pi_over_log_neg
    (p : Nat) (hp : Nat.Prime p) :
    routeAPrimePoissonSymbol p (Real.pi / Real.log (p : Real)) < 0 := by
  let r : Real := 1 / Real.sqrt (p : Real)
  have hpcast : (1 : Real) < (p : Real) := by exact_mod_cast hp.one_lt
  have hlog : Real.log (p : Real) ≠ 0 := by
    have : 1 < (p : Real) := hpcast
    exact ne_of_gt (Real.log_pos this)
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (p : Real) by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (1 - Real.sqrt (p : Real))]
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (show 0 < (p : Real) by positivity))]
    simpa using hsqrt
  unfold routeAPrimePoissonSymbol
  dsimp [r]
  have harg : Real.log (p : Real) * (Real.pi / Real.log (p : Real)) = Real.pi := by
    field_simp
  rw [harg, Real.cos_pi]
  change (1 - r ^ 2) / (1 - 2 * r * (-1) + r ^ 2) - 1 < 0
  have hd : 0 < 1 - 2 * r * (-1) + r ^ 2 := by
    nlinarith [sq_pos_of_pos (show 0 < 1 + r by linarith)]
  apply sub_neg.mpr
  apply (div_lt_iff₀ hd).2
  nlinarith [hrpos]

theorem no_single_prime_nonnegative_kernel_factor
    (p : Nat) (hp : Nat.Prime p) :
    ¬ (∀ xi : Real, 0 ≤ routeAPrimePoissonSymbol p xi) := by
  intro hnonneg
  have hneg := routeAPrimePoissonSymbol_pi_over_log_neg p hp
  linarith [hnonneg (Real.pi / Real.log (p : Real))]

theorem routeAOrbitTransform_zero_eq_zero_of_off_line
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hoff : rho.1.re ≠ 1 / 2) :
    routeAOrbitTransform geometry 0 = 0 := by
  have hraw := geometry.raw_target_values
    ⟨(1 / 2 : Complex), mem_healthyUnscaledTargetNodes_half rho.1⟩
  have htarget := healthyUnscaledTargetValue_half (rho := rho.1) rho.2 hoff
  have hzero :
      CC20YoshidaConvolution.CompactLogTest.laplaceAt
          ((convolutionIterate geometry.base geometry.orbitIndex).convolution
            geometry.correction) (1 / 2 : Complex) = 0 := by
    rw [hraw, htarget]
  have hcenter := selectedOwner_laplaceAt_sourceTest_centered_eq_zero
    geometry.base geometry.correction geometry.orbitIndex (1 / 2 : Complex) hzero
  rw [routeAOrbitTransform_eq_selectedSourceLaplace geometry 0]
  rw [geometry.selected_owner_test]
  simpa using hcenter


end
end C1RouteAJointSymbolSquareScreen3082
end Source
end ConnesWeilRH
