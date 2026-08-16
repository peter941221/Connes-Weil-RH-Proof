import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# C1XiGammaEulerProduct - the locally uniform Euler-product brick

This module isolates the convergent part of the Gauss/Gamma route.  The
corrected factors are

`(1 + z / (n + 1)) * exp (-(z / (n + 1)))`.

Their linear terms cancel, so the factor minus one is quadratically small in
`z / (n + 1)`.  That estimate is the input to Mathlib's locally uniform
infinite-product theorem.  The module closes the corrected Gamma product and
its digamma-series readback, but not Gauss' integral or the Gamma_R contour
readback.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGammaEulerProduct

open Complex
open Filter
open Metric
open Set
open scoped Topology

noncomputable section

/-- The genus-one corrected Euler factor, indexed from `n + 1`. -/
noncomputable def correctedEulerFactor (z : Complex) (n : Nat) : Complex :=
  (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1)))

/-- The perturbation of one carried by a corrected Euler factor. -/
noncomputable def correctedEulerRemainder (z : Complex) (n : Nat) : Complex :=
  correctedEulerFactor z n - 1

/-- The finite prefix of the corrected Euler product. -/
noncomputable def correctedEulerPartialProduct (z : Complex) (N : Nat) : Complex :=
  ∏ n ∈ Finset.range N, correctedEulerFactor z n

/-- The finite linear part of a corrected Euler prefix. -/
noncomputable def correctedEulerLinearProduct (z : Complex) (N : Nat) : Complex :=
  ∏ n ∈ Finset.range N, (1 + z / (n + 1))

/-- A finite corrected Euler prefix separates into its linear product and the
exponential of the corresponding harmonic correction. -/
theorem correctedEulerPartialProduct_eq_linear_mul_exp_harmonic
    (z : Complex) (N : Nat) :
    correctedEulerPartialProduct z N =
      correctedEulerLinearProduct z N * Complex.exp (-z * (harmonic N : Complex)) := by
  induction N with
  | zero =>
      simp [correctedEulerPartialProduct, correctedEulerLinearProduct]
  | succ N ih =>
      have hpartial : correctedEulerPartialProduct z (N + 1) =
          correctedEulerPartialProduct z N * correctedEulerFactor z N := by
        simp [correctedEulerPartialProduct, Finset.prod_range_succ]
      have hlinear : correctedEulerLinearProduct z (N + 1) =
          correctedEulerLinearProduct z N * (1 + z / (N + 1)) := by
        simp [correctedEulerLinearProduct, Finset.prod_range_succ]
      rw [hpartial, ih, hlinear]
      unfold correctedEulerFactor
      calc
        (correctedEulerLinearProduct z N * Complex.exp (-z * (harmonic N : Complex))) *
            ((1 + z / (N + 1)) * Complex.exp (-(z / (N + 1)))) =
            (correctedEulerLinearProduct z N * (1 + z / (N + 1))) *
              (Complex.exp (-z * (harmonic N : Complex)) *
                Complex.exp (-(z / (N + 1)))) := by ring
        _ = (correctedEulerLinearProduct z N * (1 + z / (N + 1))) *
              Complex.exp (-z * (harmonic N : Complex) + -(z / (N + 1))) := by
          rw [← Complex.exp_add]
        _ = (correctedEulerLinearProduct z N * (1 + z / (N + 1))) *
              Complex.exp (-z * (harmonic (N + 1) : Complex)) := by
          congr 2
          rw [harmonic_succ]
          push_cast
          ring

/-- The linear finite prefix is the shifted Gamma denominator divided by
`N!`.  This statement is purely finite algebra and has no limiting content. -/
theorem correctedEulerLinearProduct_mul_factorial_eq_shiftedProduct
    (z : Complex) (N : Nat) :
    correctedEulerLinearProduct z N * ((Nat.factorial N : Nat) : Complex) =
      ∏ j ∈ Finset.range N, (z + 1 + j) := by
  induction N with
  | zero =>
      simp [correctedEulerLinearProduct]
  | succ N ih =>
      rw [show correctedEulerLinearProduct z (N + 1) =
          correctedEulerLinearProduct z N * (1 + z / (N + 1)) by
            simp [correctedEulerLinearProduct, Finset.prod_range_succ],
        Nat.factorial_succ, Nat.cast_mul, Finset.prod_range_succ]
      calc
        (correctedEulerLinearProduct z N * (1 + z / (N + 1))) *
            (((N + 1 : Nat) : Complex) * ((Nat.factorial N : Nat) : Complex)) =
            (correctedEulerLinearProduct z N * ((Nat.factorial N : Nat) : Complex)) *
              (z + 1 + N) := by
          have hden : ((N + 1 : Nat) : Complex) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
          push_cast
          field_simp [hden]
          ring
        _ = (∏ j ∈ Finset.range N, (z + 1 + j)) * (z + 1 + N) := by
          rw [ih]

private theorem shiftedGammaFactor_ne_zero_of_re_pos
    {z : Complex} (hz : 0 < z.re) (j : Nat) :
    z + 1 + (j : Complex) ≠ 0 := by
  intro hzero
  have hreal := congrArg Complex.re hzero
  have hpos : 0 < z.re + 1 + (j : Real) := by positivity
  simp only [add_re, one_re, zero_re, Complex.natCast_re] at hreal
  linarith

/-- The finite linear prefix is exactly the reciprocal Gamma approximation
with the matching finite shift. -/
theorem correctedEulerLinearProduct_eq_GammaSeq
    {z : Complex} (hz : 0 < z.re) {N : Nat} (hN : N ≠ 0) :
    correctedEulerLinearProduct z N =
      (N : Complex) ^ (z + 1) /
        ((z + 1 + (N : Complex)) * Complex.GammaSeq (z + 1) N) := by
  have hprefix : ∏ j ∈ Finset.range N, (z + 1 + j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact shiftedGammaFactor_ne_zero_of_re_pos hz j
  have hshift : z + 1 + (N : Complex) ≠ 0 :=
    shiftedGammaFactor_ne_zero_of_re_pos hz N
  have hNcomplex : (N : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpow : (N : Complex) ^ (z + 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hNcomplex)
  have hfactorial : ((Nat.factorial N : Nat) : Complex) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hproductSucc :
      (∏ j ∈ Finset.range (N + 1), (z + 1 + j)) =
        (∏ j ∈ Finset.range N, (z + 1 + j)) * (z + 1 + N) := by
    rw [Finset.prod_range_succ]
  have hlinear := correctedEulerLinearProduct_mul_factorial_eq_shiftedProduct z N
  rw [Complex.GammaSeq]
  rw [hproductSucc]
  field_simp [hprefix, hshift, hpow, hfactorial]
  rw [← hlinear]

/-- A finite corrected Euler prefix expressed through the matching Gamma
approximation and harmonic correction. -/
theorem correctedEulerPartialProduct_eq_GammaSeq
    {z : Complex} (hz : 0 < z.re) {N : Nat} (hN : N ≠ 0) :
    correctedEulerPartialProduct z N =
      ((N : Complex) ^ (z + 1) /
        ((z + 1 + (N : Complex)) * Complex.GammaSeq (z + 1) N)) *
          Complex.exp (-z * (harmonic N : Complex)) := by
  rw [correctedEulerPartialProduct_eq_linear_mul_exp_harmonic,
    correctedEulerLinearProduct_eq_GammaSeq hz hN]

private theorem tendsto_harmonic_sub_log_complex :
    Tendsto (fun n : Nat =>
      (harmonic n : Complex) - Complex.log (n : Complex)) atTop
        (𝓝 (Real.eulerMascheroniConstant : Complex)) := by
  have hreal := Real.tendsto_harmonic_sub_log
  have hcomplex :
      Tendsto (fun n : Nat =>
        Complex.ofReal ((harmonic n : Real) - Real.log n)) atTop
          (𝓝 (Real.eulerMascheroniConstant : Complex)) :=
    (Complex.continuous_ofReal.tendsto _).comp hreal
  apply hcomplex.congr'
  filter_upwards with n
  rw [Complex.ofReal_sub]
  congr 1
  · norm_cast

private theorem tendsto_correctedEuler_harmonic_exponential (z : Complex) :
    Tendsto (fun n : Nat =>
      Complex.exp (-z * ((harmonic n : Complex) - Complex.log (n : Complex)))) atTop
        (𝓝 (Complex.exp (-z * (Real.eulerMascheroniConstant : Complex))) ) := by
  exact ((tendsto_const_nhds (x := -z)).mul tendsto_harmonic_sub_log_complex).cexp

private theorem gammaSeq_shifted_ne_zero_of_re_pos
    {z : Complex} (hz : 0 < z.re) {N : Nat} (hN : N ≠ 0) :
    Complex.GammaSeq (z + 1) N ≠ 0 := by
  unfold Complex.GammaSeq
  apply div_ne_zero
  · apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Nat.cast_ne_zero.mpr hN : (N : Complex) ≠ 0))
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact shiftedGammaFactor_ne_zero_of_re_pos hz j

private theorem correctedEulerPartialProduct_eq_normalizedGammaSeq
    {z : Complex} (hz : 0 < z.re) {N : Nat} (hN : N ≠ 0) :
    correctedEulerPartialProduct z N =
      ((N : Complex) / ((N : Complex) + (1 + z))) *
        (Complex.GammaSeq (z + 1) N)⁻¹ *
          Complex.exp (-z * ((harmonic N : Complex) - Complex.log (N : Complex))) := by
  have hNcomplex : (N : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hshift : z + 1 + (N : Complex) ≠ 0 :=
    shiftedGammaFactor_ne_zero_of_re_pos hz N
  have hshift' : (N : Complex) + (1 + z) ≠ 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hshift
  have hgamma : Complex.GammaSeq (z + 1) N ≠ 0 :=
    gammaSeq_shifted_ne_zero_of_re_pos hz hN
  rw [correctedEulerPartialProduct_eq_GammaSeq hz hN,
    Complex.cpow_add _ _ hNcomplex, Complex.cpow_one,
    Complex.cpow_def_of_ne_zero hNcomplex]
  have hexp :
      Complex.exp (Complex.log (N : Complex) * z) *
          Complex.exp (-z * (harmonic N : Complex)) =
        Complex.exp (-z * ((harmonic N : Complex) - Complex.log (N : Complex))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    ((Complex.exp (Complex.log (N : Complex) * z) * (N : Complex)) /
          ((z + 1 + (N : Complex)) * Complex.GammaSeq (z + 1) N)) *
        Complex.exp (-z * (harmonic N : Complex)) =
        ((N : Complex) / ((N : Complex) + (1 + z))) *
          (Complex.GammaSeq (z + 1) N)⁻¹ *
            (Complex.exp (Complex.log (N : Complex) * z) *
              Complex.exp (-z * (harmonic N : Complex))) := by
          field_simp [hshift, hshift', hgamma]
          ring
    _ = ((N : Complex) / ((N : Complex) + (1 + z))) *
          (Complex.GammaSeq (z + 1) N)⁻¹ *
            Complex.exp (-z * ((harmonic N : Complex) - Complex.log (N : Complex))) := by
          rw [hexp]

private theorem tendsto_normalizedGammaSeq_of_re_pos
    {z : Complex} (hz : 0 < z.re) :
    Tendsto (fun N : Nat =>
      ((N : Complex) / ((N : Complex) + (1 + z))) *
        (Complex.GammaSeq (z + 1) N)⁻¹ *
          Complex.exp (-z * ((harmonic N : Complex) - Complex.log (N : Complex)))) atTop
        (𝓝 ((Complex.Gamma (z + 1))⁻¹ *
          Complex.exp (-z * (Real.eulerMascheroniConstant : Complex)))) := by
  have hratio :
      Tendsto (fun N : Nat => (N : Complex) / ((N : Complex) + (1 + z))) atTop
        (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 + z)
  have hGamma : Complex.Gamma (z + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have hgammaSeq :
      Tendsto (fun N : Nat => (Complex.GammaSeq (z + 1) N)⁻¹) atTop
        (𝓝 (Complex.Gamma (z + 1))⁻¹) :=
    (Complex.GammaSeq_tendsto_Gamma (z + 1)).inv₀ hGamma
  simpa using
    ((hratio.mul hgammaSeq).mul (tendsto_correctedEuler_harmonic_exponential z))

private theorem tendsto_correctedEulerPartialProduct_gamma_of_re_pos
    {z : Complex} (hz : 0 < z.re) :
    Tendsto (correctedEulerPartialProduct z) atTop
      (𝓝 ((Complex.Gamma (z + 1))⁻¹ *
        Complex.exp (-z * (Real.eulerMascheroniConstant : Complex))) ) := by
  apply (tendsto_normalizedGammaSeq_of_re_pos hz).congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact (correctedEulerPartialProduct_eq_normalizedGammaSeq hz hN).symm

private theorem correctedEulerRemainder_eq_exp_remainder_add_mul
    (z : Complex) (n : Nat) :
    correctedEulerRemainder z n =
      (Complex.exp (-(z / (n + 1))) - 1 + z / (n + 1)) +
        (z / (n + 1)) * (Complex.exp (-(z / (n + 1))) - 1) := by
  unfold correctedEulerRemainder correctedEulerFactor
  ring

private theorem norm_div_nat_add_one (z : Complex) (n : Nat) :
    ‖z / (n + 1)‖ = ‖z‖ / (n + 1 : Real) := by
  rw [norm_div]
  have hden : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hden, norm_natCast]
  norm_num

private theorem correctedEulerRemainder_norm_le_of_norm_le_one
    {w : Complex} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have hfirst : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    convert Complex.norm_exp_sub_one_sub_id_le (x := -w) (by simpa using hw) using 1
    · ring_nf
    · simp
  have hsecond : ‖Complex.exp (-w) - 1‖ ≤ 2 * ‖w‖ := by
    simpa using Complex.norm_exp_sub_one_le (x := -w) (by simpa using hw)
  rw [show (1 + w) * Complex.exp (-w) - 1 =
      (Complex.exp (-w) - 1 + w) + w * (Complex.exp (-w) - 1) by ring]
  calc
    ‖(Complex.exp (-w) - 1 + w) + w * (Complex.exp (-w) - 1)‖ ≤
        ‖Complex.exp (-w) - 1 + w‖ + ‖w * (Complex.exp (-w) - 1)‖ :=
      norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
      apply add_le_add hfirst
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hsecond (norm_nonneg w)
    _ = 3 * ‖w‖ ^ 2 := by ring

theorem correctedEulerRemainder_norm_le
    {R : Real} {z : Complex} (hz : ‖z‖ ≤ R)
    {n : Nat} (hn : R ≤ (n + 1 : Real)) :
    ‖correctedEulerRemainder z n‖ ≤
      3 * (R / (n + 1 : Real)) ^ 2 := by
  have hden : 0 < (n + 1 : Real) := by positivity
  have hw : ‖z / (n + 1)‖ ≤ 1 := by
    rw [norm_div_nat_add_one]
    exact (div_le_iff₀ hden).2 (hz.trans (by simpa using hn))
  rw [show correctedEulerRemainder z n =
      (1 + (z / (n + 1))) * Complex.exp (-(z / (n + 1))) - 1 by
        rfl]
  calc
    ‖(1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1‖ ≤
        3 * ‖z / (n + 1)‖ ^ 2 :=
      correctedEulerRemainder_norm_le_of_norm_le_one hw
    _ = 3 * (‖z‖ / (n + 1 : Real)) ^ 2 := by
      rw [norm_div_nat_add_one]
    _ ≤ 3 * (R / (n + 1 : Real)) ^ 2 := by
      gcongr

private theorem summable_three_mul_sq_inv (R : Real) :
    Summable (fun n : Nat => 3 * (R / (n + 1 : Real)) ^ 2) := by
  have hs : Summable (fun n : Nat => (1 / (n + 1 : Real)) ^ 2) := by
    have hbase : Summable (fun n : Nat => 1 / (n : Real) ^ (2 : Real)) :=
      (Real.summable_one_div_nat_rpow (p := (2 : Real))).2 (by norm_num)
    simpa [one_div, div_pow] using (summable_nat_add_iff 1).2 hbase
  convert (hs.mul_left (3 * R ^ 2)) using 1 with n
  field_simp

private theorem eventually_correctedEulerRemainder_bound
    {R : Real} :
    ∀ᶠ n : Nat in atTop, ∀ z ∈ ball (0 : Complex) R,
      ‖correctedEulerRemainder z n‖ ≤ 3 * (R / (n + 1 : Real)) ^ 2 := by
  filter_upwards [eventually_ge_atTop ⌈R⌉₊] with n hn z hz
  apply correctedEulerRemainder_norm_le
  · have hz' : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
    exact le_of_lt hz'
  · calc
      R ≤ (n : Real) := Nat.ceil_le.1 hn
      _ ≤ (n + 1 : Real) := by linarith

private theorem continuousOn_correctedEulerRemainder (n : Nat) :
    ContinuousOn (correctedEulerRemainder · n) (ball (0 : Complex) R) := by
  unfold correctedEulerRemainder correctedEulerFactor
  fun_prop

theorem correctedEulerFactor_hasProdLocallyUniformlyOn_ball
    {R : Real} :
    HasProdLocallyUniformlyOn
      (fun n z => correctedEulerFactor z n)
      (fun z => ∏' n, correctedEulerFactor z n)
      (ball (0 : Complex) R) := by
  have hbound := eventually_correctedEulerRemainder_bound (R := R)
  have hfactor : ∀ n : Nat, ∀ z : Complex,
      1 + correctedEulerRemainder z n = correctedEulerFactor z n := by
    intro n z
    unfold correctedEulerRemainder
    ring
  have hproduct := Summable.hasProdLocallyUniformlyOn_nat_one_add
      (f := fun (n : Nat) (z : Complex) => correctedEulerRemainder z n)
      (K := ball (0 : Complex) R) isOpen_ball
      (summable_three_mul_sq_inv R) hbound
      (fun n => continuousOn_correctedEulerRemainder n)
  have hproduct' : HasProdLocallyUniformlyOn
      (fun n z => correctedEulerFactor z n)
      (fun z => ∏' n : Nat, (1 + correctedEulerRemainder z n))
      (ball (0 : Complex) R) :=
    hproduct.congr fun s z _ => by
      apply Finset.prod_congr rfl
      intro n _
      exact hfactor n z
  have htprod : (fun z => ∏' n : Nat, (1 + correctedEulerRemainder z n)) =
      (fun z => ∏' n : Nat, correctedEulerFactor z n) := by
    funext z
    apply congrArg tprod
    funext n
    exact hfactor n z
  rwa [htprod] at hproduct'

theorem correctedEulerFactor_multipliableLocallyUniformlyOn_ball
    {R : Real} :
    MultipliableLocallyUniformlyOn
      (fun n z => correctedEulerFactor z n)
      (ball (0 : Complex) R) :=
  (correctedEulerFactor_hasProdLocallyUniformlyOn_ball (R := R)).multipliableLocallyUniformlyOn

/-- The fixed-point corrected Euler factors are multipliable. -/
theorem correctedEulerFactor_multipliable (z : Complex) :
    Multipliable (correctedEulerFactor z) := by
  obtain ⟨R, hR, hzR⟩ : ∃ R : Real, 0 < R ∧ z ∈ ball (0 : Complex) R := by
    refine ⟨‖z‖ + 1, by positivity, ?_⟩
    simp [mem_ball, dist_zero_right]
  exact (correctedEulerFactor_multipliableLocallyUniformlyOn_ball (R := R)).multipliable hzR

/-- The finite corrected Euler prefixes converge to their infinite product. -/
theorem tendsto_correctedEulerPartialProduct_tprod (z : Complex) :
    Tendsto (correctedEulerPartialProduct z) atTop
      (𝓝 (∏' n : Nat, correctedEulerFactor z n)) := by
  simpa only [correctedEulerPartialProduct] using
    (correctedEulerFactor_multipliable z).tendsto_prod_tprod_nat

/-- Euler's corrected product for the reciprocal Gamma function on the open
right half-plane. -/
theorem correctedEulerFactor_tprod_eq_exp_div_Gamma
    {z : Complex} (hz : 0 < z.re) :
    ∏' n : Nat, correctedEulerFactor z n =
      Complex.exp (-z * (Real.eulerMascheroniConstant : Complex)) /
        Complex.Gamma (z + 1) := by
  have hprefix := tendsto_correctedEulerPartialProduct_tprod z
  have hgamma := tendsto_correctedEulerPartialProduct_gamma_of_re_pos hz
  have hEq := tendsto_nhds_unique hprefix hgamma
  simpa [div_eq_mul_inv, mul_comm] using hEq

/-- Every corrected Euler factor is nonzero on the open right half-plane. -/
theorem correctedEulerFactor_ne_zero_of_re_pos
    (n : Nat) {z : Complex} (hz : 0 < z.re) :
    correctedEulerFactor z n ≠ 0 := by
  unfold correctedEulerFactor
  apply mul_ne_zero
  · intro hlinear
    have hreal := congrArg Complex.re hlinear
    have hcast : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
      simp only [Nat.cast_add, Nat.cast_one]
    have hdivpos : 0 < (z / ((n : Complex) + 1)).re := by
      rw [hcast, Complex.div_natCast_re]
      exact div_pos hz (by positivity)
    simp only [add_re, one_re, zero_re] at hreal
    linarith
  · exact Complex.exp_ne_zero _

/-- The corrected Euler factor is entire. -/
theorem differentiable_correctedEulerFactor (n : Nat) :
    Differentiable Complex (correctedEulerFactor · n) := by
  unfold correctedEulerFactor
  fun_prop

/-- The logarithmic derivative after the linear Euler correction.

The two terms on the right have equal `1 / (n + 1)` leading behaviour, so
their difference is quadratically summable in `n`. -/
theorem logDeriv_correctedEulerFactor
    (n : Nat) {z : Complex} (hz : 0 < z.re) :
    logDeriv (correctedEulerFactor · n) z =
      1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1) := by
  have hcast : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
    simp only [Nat.cast_add, Nat.cast_one]
  have hden : (n : Complex) + 1 ≠ 0 := by
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hsum : (n : Complex) + 1 + z ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < (n : Real) + 1 + z.re := by positivity
    simp only [add_re, one_re, zero_re, Complex.natCast_re] at hreal
    linarith
  have hlinear : HasDerivAt (fun w : Complex => 1 + w / ((n : Complex) + 1))
      (1 / ((n : Complex) + 1)) z := by
    convert (hasDerivAt_const z (1 : Complex)).add
      ((hasDerivAt_id z).div_const ((n : Complex) + 1)) using 1; ring
  have hnegative : HasDerivAt (fun w : Complex => -(w / ((n : Complex) + 1)))
      (-(1 / ((n : Complex) + 1))) z := by
    simpa using ((hasDerivAt_id z).div_const ((n : Complex) + 1)).neg
  have hexp : HasDerivAt (fun w : Complex => Complex.exp (-(w / ((n : Complex) + 1))) )
      (Complex.exp (-(z / ((n : Complex) + 1))) * (-(1 / ((n : Complex) + 1)))) z := by
    simpa using hnegative.cexp
  unfold correctedEulerFactor
  rw [logDeriv_mul z]
  · rw [logDeriv_apply, hlinear.deriv, logDeriv_apply, hexp.deriv]
    field_simp [hden, hsum, Complex.exp_ne_zero]
    ring
  · intro hzero
    apply correctedEulerFactor_ne_zero_of_re_pos n hz
    unfold correctedEulerFactor
    rw [hzero, zero_mul]
  · exact Complex.exp_ne_zero _
  · exact hlinear.differentiableAt
  · exact hexp.differentiableAt

/-- The corrected single-factor logarithmic derivatives are absolutely summable
on the open right half-plane. -/
theorem summable_logDeriv_correctedEulerFactor
    {z : Complex} (hz : 0 < z.re) :
    Summable (fun n : Nat => logDeriv (correctedEulerFactor · n) z) := by
  refine (summable_pow_div_add z 2 1 (by norm_num)).of_norm_bounded ?_
  intro n
  have hcast : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
    simp only [Nat.cast_add, Nat.cast_one]
  have hden : (n : Complex) + 1 ≠ 0 := by
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hsum : (n : Complex) + 1 + z ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < (n : Real) + 1 + z.re := by positivity
    simp only [add_re, one_re, zero_re, Complex.natCast_re] at hreal
    linarith
  have hnorm : ‖(n : Complex) + 1‖ ≤ ‖(n : Complex) + 1 + z‖ := by
    calc
      ‖(n : Complex) + 1‖ = (n : Real) + 1 := by
        rw [hcast, norm_natCast]
        norm_num
      _ ≤ (n : Real) + 1 + z.re := by linarith
      _ = ((n : Complex) + 1 + z).re := by
        simp only [add_re, one_re, Complex.natCast_re]
      _ ≤ ‖(n : Complex) + 1 + z‖ := Complex.re_le_norm _
  have hnorm_den : 0 < ‖(n : Complex) + 1‖ := norm_pos_iff.mpr hden
  rw [logDeriv_correctedEulerFactor n hz]
  have hrewrite :
      1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1) =
        -(z / (((n : Complex) + 1) * ((n : Complex) + 1 + z))) := by
    field_simp [hden, hsum]
    ring
  rw [hrewrite, norm_neg, norm_div, norm_mul]
  calc
    ‖z‖ / (‖(n : Complex) + 1‖ * ‖(n : Complex) + 1 + z‖) ≤
        ‖z‖ / (‖(n : Complex) + 1‖ * ‖(n : Complex) + 1‖) :=
      div_le_div_of_nonneg_left (norm_nonneg z)
        (mul_pos hnorm_den hnorm_den)
        (mul_le_mul_of_nonneg_left hnorm hnorm_den.le)
    _ = ‖z / ((n : Complex) + 1) ^ 2‖ := by
      rw [norm_div, norm_pow]
      ring
    _ = ‖z / ((n : Complex) + (1 : Nat)) ^ 2‖ := by norm_num

theorem correctedEulerFactor_tprod_ne_zero
    {z : Complex} (hz : 0 < z.re) :
    ∏' n : Nat, correctedEulerFactor z n ≠ 0 := by
  have hsum : Summable (fun n : Nat => ‖correctedEulerRemainder z n‖) := by
    obtain ⟨R, hR, hzR⟩ : ∃ R : Real, 0 < R ∧ z ∈ ball (0 : Complex) R := by
      refine ⟨‖z‖ + 1, by positivity, ?_⟩
      simp [mem_ball, dist_zero_right]
    have hbound := eventually_correctedEulerRemainder_bound (R := R)
    have hdom : ∀ᶠ n : Nat in atTop,
        ‖correctedEulerRemainder z n‖ ≤ 3 * (R / (n + 1 : Real)) ^ 2 :=
      by
        filter_upwards [hbound] with n hn
        exact hn z hzR
    have hrem : Summable (fun n : Nat => correctedEulerRemainder z n) :=
      (summable_three_mul_sq_inv R).of_norm_bounded_eventually_nat hdom
    exact hrem.norm
  have hne : ∀ n : Nat, 1 + correctedEulerRemainder z n ≠ 0 := by
    intro n hzero
    have hfactor : correctedEulerFactor z n = 0 := by
      simpa [correctedEulerRemainder] using hzero
    unfold correctedEulerFactor at hfactor
    rcases mul_eq_zero.mp hfactor with hlinear | hexp
    · have hcast : (n : Complex) + 1 = ((n + 1 : Nat) : Complex) := by
        simp only [Nat.cast_add, Nat.cast_one]
      rw [hcast] at hlinear
      have hreal := congrArg Complex.re hlinear
      have hdivpos : 0 < (z / ((n + 1 : Nat) : Complex)).re := by
        rw [Complex.div_natCast_re]
        exact div_pos hz (by positivity)
      simp only [add_re, one_re, zero_re] at hreal
      linarith
    · exact Complex.exp_ne_zero _ hexp
  have hprod := tprod_one_add_ne_zero_of_summable hne hsum
  have hfactor_eq : (fun n : Nat => 1 + correctedEulerRemainder z n) =
      (fun n : Nat => correctedEulerFactor z n) := by
    funext n
    unfold correctedEulerRemainder
    ring
  rw [← hfactor_eq]
  exact hprod

/-- Local uniform convergence and the quadratic derivative bound justify
termwise logarithmic differentiation of the corrected Euler product. -/
theorem logDeriv_tprod_correctedEulerFactor
    {z : Complex} (hz : 0 < z.re) :
    logDeriv (fun w : Complex => ∏' n : Nat, correctedEulerFactor w n) z =
      ∑' n : Nat, (1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1)) := by
  obtain ⟨R, hR, hzR⟩ : ∃ R : Real, 0 < R ∧ z ∈ ball (0 : Complex) R := by
    refine ⟨‖z‖ + 1, by positivity, ?_⟩
    simp [mem_ball, dist_zero_right]
  change logDeriv (∏' n : Nat, correctedEulerFactor · n) z = _
  calc
    logDeriv (∏' n : Nat, correctedEulerFactor · n) z =
        ∑' n : Nat, logDeriv (correctedEulerFactor · n) z :=
      logDeriv_tprod_eq_tsum isOpen_ball hzR
        (fun n => correctedEulerFactor_ne_zero_of_re_pos n hz)
        (fun n => (differentiable_correctedEulerFactor n).differentiableOn)
        (summable_logDeriv_correctedEulerFactor hz)
        (correctedEulerFactor_multipliableLocallyUniformlyOn_ball (R := R))
        (correctedEulerFactor_tprod_ne_zero hz)
    _ = ∑' n : Nat,
        (1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1)) := by
      apply tsum_congr
      intro n
      exact logDeriv_correctedEulerFactor n hz

/-- The logarithmic derivative of the corrected product read back through the
reciprocal-Gamma identity. -/
theorem correctedEulerLogDeriv_tprod_eq_exp_div_Gamma
    {z : Complex} (hz : 0 < z.re) :
    logDeriv (fun w : Complex => ∏' n : Nat, correctedEulerFactor w n) z =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma (z + 1) := by
  have hpos : ∀ᶠ w : Complex in 𝓝 z, 0 < w.re :=
    (Complex.continuous_re.tendsto z).eventually (eventually_gt_nhds hz)
  have hEq :
      (fun w : Complex => ∏' n : Nat, correctedEulerFactor w n) =ᶠ[𝓝 z]
        (fun w : Complex =>
          Complex.exp (-w * (Real.eulerMascheroniConstant : Complex)) /
            Complex.Gamma (w + 1)) := by
    filter_upwards [hpos] with w hw
    exact correctedEulerFactor_tprod_eq_exp_div_Gamma hw
  have hshift : ∀ m : Nat, z + 1 ≠ -(m : Complex) := by
    intro m hzero
    have hreal := congrArg Complex.re hzero
    simp only [add_re, one_re, neg_re, Complex.natCast_re] at hreal
    linarith
  have hgamma_ne : Complex.Gamma (z + 1) ≠ 0 :=
    Complex.Gamma_ne_zero hshift
  have hgamma_diff :
      DifferentiableAt Complex (fun w : Complex => Complex.Gamma (w + 1)) z := by
    simpa only [Function.comp_apply] using
      (Complex.differentiableAt_Gamma (z + 1) hshift).comp z (by fun_prop)
  have hexp_diff :
      DifferentiableAt Complex
        (fun w : Complex => Complex.exp (-w * (Real.eulerMascheroniConstant : Complex))) z := by
    fun_prop
  have hexp_log :
      logDeriv
          (fun w : Complex =>
            Complex.exp (-w * (Real.eulerMascheroniConstant : Complex))) z =
        -(Real.eulerMascheroniConstant : Complex) := by
    have harg : HasDerivAt
        (fun w : Complex => -w * (Real.eulerMascheroniConstant : Complex))
        (-(Real.eulerMascheroniConstant : Complex)) z := by
      convert ((hasDerivAt_id z).neg.mul_const
        (Real.eulerMascheroniConstant : Complex)) using 1; ring
    have hcomp :
        (fun w : Complex =>
          Complex.exp (-w * (Real.eulerMascheroniConstant : Complex))) =
          Complex.exp ∘ (fun w : Complex =>
            -w * (Real.eulerMascheroniConstant : Complex)) := by
      rfl
    rw [hcomp, logDeriv_comp (by fun_prop) harg.differentiableAt,
      Complex.logDeriv_exp]
    simpa only [Pi.one_apply, one_mul] using harg.deriv
  have hgamma_log :
      logDeriv (fun w : Complex => Complex.Gamma (w + 1)) z =
        Complex.digamma (z + 1) := by
    have hcomp :
        (fun w : Complex => Complex.Gamma (w + 1)) =
          Complex.Gamma ∘ (fun w : Complex => w + 1) := by
      rfl
    rw [hcomp, logDeriv_comp (f := Complex.Gamma)
      (g := fun w : Complex => w + 1) (x := z)
      (Complex.differentiableAt_Gamma (z + 1) hshift) (by fun_prop)]
    simp [Complex.digamma_def]
  have hright :
      logDeriv
          (fun w : Complex =>
            Complex.exp (-w * (Real.eulerMascheroniConstant : Complex)) /
              Complex.Gamma (w + 1)) z =
        -(Real.eulerMascheroniConstant : Complex) - Complex.digamma (z + 1) := by
    rw [logDeriv_div
      (f := fun w : Complex =>
        Complex.exp (-w * (Real.eulerMascheroniConstant : Complex)))
      (g := fun w : Complex => Complex.Gamma (w + 1)) z
      (Complex.exp_ne_zero _) hgamma_ne hexp_diff hgamma_diff,
      hexp_log, hgamma_log]
  calc
    logDeriv (fun w : Complex => ∏' n : Nat, correctedEulerFactor w n) z =
        logDeriv
          (fun w : Complex =>
            Complex.exp (-w * (Real.eulerMascheroniConstant : Complex)) /
              Complex.Gamma (w + 1)) z := by
      simp only [logDeriv_apply]
      rw [hEq.deriv_eq, correctedEulerFactor_tprod_eq_exp_div_Gamma hz]
    _ = _ := hright

/-- The corrected Euler logarithmic derivative is the classical digamma series. -/
theorem correctedEulerDigammaSeries
    {z : Complex} (hz : 0 < z.re) :
    ∑' n : Nat, (1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1)) =
      -(Real.eulerMascheroniConstant : Complex) - Complex.digamma (z + 1) := by
  calc
    ∑' n : Nat, (1 / (((n : Complex) + 1) + z) - 1 / ((n : Complex) + 1)) =
        logDeriv (fun w : Complex => ∏' n : Nat, correctedEulerFactor w n) z :=
      (logDeriv_tprod_correctedEulerFactor hz).symm
    _ = _ := correctedEulerLogDeriv_tprod_eq_exp_div_Gamma hz

end
end C1XiGammaEulerProduct
end Source
end ConnesWeilRH
