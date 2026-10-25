import ConnesWeilRH.Dev.C1DetectorHeightCost3095
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cost of the actual detector's opposite interpolation values

The lower bound of record 3063 is proved on the raw factor of the actual
orbit geometry. Support and differing finite targets force inverse-gap L1
cost. This is a necessary cost, not an upper bound, zero-existence theorem,
or selected Weil-sign theorem.
-/

namespace ConnesWeilRH.Source.C1DetectorNearCollisionCost3096

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaCriticalContraction.CompactLogTest
open CC20YoshidaNearZeros
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalProfileReadback
open C1HealthyYoshidaUnscaledOrbit

noncomputable section

theorem laplace_derivative_norm_le_mass (f : CompactLogTest) (B A : Real)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s : Complex) (hre : |s.re| ≤ A) :
    ‖deriv (laplaceAt f) s‖ ≤ B * Real.exp (A * B) * l1Mass f := by
  rw [(C1XiResidue.hasDerivAt_laplaceAt f s).deriv]
  let k : Real → Complex := fun x =>
    (Complex.exp (s * (x : Complex)) * (x : Complex)) * f.test x
  have hk : Continuous k := by
    exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).mul
        Complex.continuous_ofReal).mul f.test.continuous
  have hcompact : HasCompactSupport k := f.compactSupport.mul_left
  have hpoint (x : Real) : ‖k x‖ ≤ (B * Real.exp (A * B)) * ‖f.test x‖ := by
    by_cases hx : f.test x = 0
    · simp [k, hx]
    · have hxs := hsupport (Function.mem_support.mpr hx)
      have habs : |x| ≤ B := abs_le.mpr hxs
      have hexp : Real.exp (s.re * x) ≤ Real.exp (A * B) := by
        apply Real.exp_le_exp.mpr
        calc
          s.re * x ≤ |s.re * x| := le_abs_self _
          _ = |s.re| * |x| := abs_mul _ _
          _ ≤ A * B := mul_le_mul hre habs (abs_nonneg _) ((abs_nonneg _).trans hre)
      simp only [k, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.norm_real, Real.norm_eq_abs]
      calc
        Real.exp (s.re * x) * |x| * ‖f.test x‖ ≤
            Real.exp (A * B) * B * ‖f.test x‖ := by
          gcongr
        _ = _ := by ring
  calc
    ‖∫ x : Real, k x‖ ≤ ∫ x : Real, ‖k x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Real, (B * Real.exp (A * B)) * ‖f.test x‖ :=
      integral_mono (hk.integrable_of_hasCompactSupport hcompact).norm
        (f.test.integrable.norm.const_mul _) hpoint
    _ = _ := by rw [integral_const_mul]; rfl

theorem laplace_gap_le_mass (f : CompactLogTest) (B A : Real)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s1 s2 : Complex) (hre1 : |s1.re| ≤ A) (hre2 : |s2.re| ≤ A) :
    ‖laplaceAt f s1 - laplaceAt f s2‖ ≤
      (B * Real.exp (A * B) * l1Mass f) * ‖s1 - s2‖ := by
  have hc : Convex Real (Complex.reCLM ⁻¹' Set.Icc (-A) A) :=
    (convex_Icc (-A) A).linear_preimage Complex.reCLM.toLinearMap
  exact hc.norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (C1XiResidue.hasDerivAt_laplaceAt f s).differentiableAt)
    (fun s hs => laplace_derivative_norm_le_mass f B A hsupport s
      (abs_le.mpr hs)) (abs_le.mp hre2) (abs_le.mp hre1)

theorem raw_factor_unit_targets
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (hoff : rho.1.re ≠ 1 / 2) :
    laplaceAt (orbitRawFactor geometry) rho.1 = 1 ∧
      laplaceAt (orbitRawFactor geometry) (1 - star rho.1) = -1 := by
  constructor
  · have h := geometry.raw_target_values
      ⟨rho.1, mem_healthyUnscaledTargetNodes_rho rho.1⟩
    simpa only [orbitRawFactor, healthyUnscaledTargetValue_rho] using h
  · have h := geometry.raw_target_values
      ⟨1 - star rho.1, mem_healthyUnscaledTargetNodes_companion rho.1⟩
    simpa only [orbitRawFactor, healthyUnscaledTargetValue_companion rho.1 hoff] using h

/-- Height and near-collision costs below concern the same raw factor. -/
theorem raw_factor_height_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    |rho.1.im| ≤ Real.exp ((geometry.orbitIndex + 2 : Nat) : Real) *
      C1ExplicitFiniteNodeCorrection.derivOrderL1 1 (orbitRawFactor geometry) := by
  have hsupp : Function.support (orbitRawFactor geometry).test ⊆
      Set.Icc (-((geometry.orbitIndex + 2 : Nat) : Real))
        (((geometry.orbitIndex + 2 : Nat) : Real)) :=
    (orbitRawFactor_support_subset geometry).trans Set.Ioo_subset_Icc_self
  have hr0 := sourceNontrivialZero_zero_lt_re rho.2
  have hr1 := sourceNontrivialZero_re_lt_one rho.2
  have ht := geometry.raw_target_values
    ⟨rho.1, mem_healthyUnscaledTargetNodes_rho rho.1⟩
  have htarget : 1 ≤ ‖laplaceAt (orbitRawFactor geometry) rho.1‖ := by
    have hvalue : laplaceAt (orbitRawFactor geometry) rho.1 = 1 := by
      simpa only [orbitRawFactor, healthyUnscaledTargetValue_rho] using ht
    rw [hvalue]
    simp
  simpa only [one_mul] using C1DetectorHeightCost3095.unit_laplace_target_height_le
    (orbitRawFactor geometry) ((geometry.orbitIndex + 2 : Nat) : Real) 1
    (by positivity) hsupp rho.1 (abs_le.mpr ⟨by linarith, hr1.le⟩) htarget

theorem opposite_targets_nodes_ne (f : CompactLogTest) (s1 s2 : Complex)
    (h1 : laplaceAt f s1 = 1) (h2 : laplaceAt f s2 = -1) : s1 ≠ s2 := by
  intro heq
  rw [heq, h2] at h1
  norm_num at h1

theorem raw_factor_inverse_gap_mass
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (hoff : rho.1.re ≠ 1 / 2) :
    1 / ((((geometry.orbitIndex + 2 : Nat) : Real) *
        Real.exp ((geometry.orbitIndex + 2 : Nat) : Real)) *
          |rho.1.re - 1 / 2|) ≤ l1Mass (orbitRawFactor geometry) := by
  let L : Real := ((geometry.orbitIndex + 2 : Nat) : Real)
  have hL : 0 < L := by dsimp [L]; positivity
  have hgap : 0 < |rho.1.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hsupp : Function.support (orbitRawFactor geometry).test ⊆ Set.Icc (-L) L :=
    (orbitRawFactor_support_subset geometry).trans Set.Ioo_subset_Icc_self
  have hr0 := sourceNontrivialZero_zero_lt_re rho.2
  have hr1 := sourceNontrivialZero_re_lt_one rho.2
  have hre1 : |rho.1.re| ≤ 1 := abs_le.mpr ⟨by linarith, hr1.le⟩
  have hre2 : |(1 - star rho.1).re| ≤ 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := laplace_gap_le_mass (orbitRawFactor geometry) L 1 hsupp
    rho.1 (1 - star rho.1) hre1 hre2
  obtain ⟨ht1, ht2⟩ := raw_factor_unit_targets geometry hoff
  have hdiff : rho.1 - (1 - star rho.1) =
      ((2 * (rho.1.re - 1 / 2) : Real) : Complex) := by
    apply Complex.ext
    · simp <;> ring
    · simp
  have hnorm : ‖rho.1 - (1 - star rho.1)‖ = 2 * |rho.1.re - 1 / 2| := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  rw [ht1, ht2, hnorm, show ‖(1 : Complex) - (-1)‖ = (2 : Real) by norm_num] at h
  simp only [one_mul] at h
  have hunit : 1 ≤ (L * Real.exp L * |rho.1.re - 1 / 2|) *
      l1Mass (orbitRawFactor geometry) := by nlinarith [h]
  exact (div_le_iff₀ (by positivity : 0 < L * Real.exp L * |rho.1.re - 1 / 2|)).mpr
    (by simpa [L, mul_comm] using hunit)

/-- A claimed uniform mass ceiling must pay the actual gap. This is a
parameterized stop rule, not a claim that any such zero exists. -/
theorem no_raw_factor_mass_cap_below_inverse_gap
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (hoff : rho.1.re ≠ 1 / 2)
    (M : Real) (hmass : l1Mass (orbitRawFactor geometry) ≤ M)
    (hprice : M < 1 / ((((geometry.orbitIndex + 2 : Nat) : Real) *
        Real.exp ((geometry.orbitIndex + 2 : Nat) : Real)) *
          |rho.1.re - 1 / 2|)) : False := by
  exact (not_lt_of_ge ((raw_factor_inverse_gap_mass geometry hoff).trans hmass)) hprice

end
end ConnesWeilRH.Source.C1DetectorNearCollisionCost3096
