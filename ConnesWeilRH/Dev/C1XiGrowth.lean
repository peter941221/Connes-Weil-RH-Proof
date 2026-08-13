import ConnesWeilRH.Source.CC20ZetaCounting

/-!
# C1XiGrowth

Task #2 of Gate 2: uniform control of the completed Riemann xi function on the
doubled Jensen circle `sphere (2 : ℂ) |2 ⋅ (T + 2)|`.

Via `CC20ZetaCounting.norm_completedRiemannXi_le_kernelMoment` it reduces to a
bound for `completedRiemannXiKernelMoment σ` on the folded half-plane
`σ >= 1 / 2`.  The functional equation supplies this fold, while the dyadic
consumer needs a `O(R log R)` exponent rather than a strip-uniform bound.
Everything here is unconditional: no RH, no `sorry`, no new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGrowth

open scoped Topology BigOperators
open CC20ZetaCounting
open MeasureTheory Set

/-- The decisive exponential Gamma moment governing the large-`t` tail of the
completed-decided kernel: with the exponent written as `1/2 - 1` structurally
equal to the checked-in real Gamma-moment identity, `a := 1/2` and `r := π`.
This is exactly the exponential moment used to integrate the large theta-kernel
branch. -/
theorem kernelGammaMoment_halfRe :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(Real.pi * t))) =
        (1 / Real.pi) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
  -- a := 1/2 gives t^(a-1) and r := π the exponential scale; exact match.
  exact integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
    (a := (1 / 2 : ℝ)) (r := Real.pi) (by norm_num) Real.pi_pos

/-- Inverting the positive coordinate transforms the small-end exponential
kernel moment into the same Gamma moment.  This is the exact identity needed
for the folded lower bound `sigma >= 1 / 2`; its uniform envelope uses
`a = 1 / 4`, not the obsolete `a = 1 / 2` endpoint from the old strip plan. -/
theorem kernelInverseGammaMoment {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ (-(a + 1)) * Real.exp (-(Real.pi * t ^ (-1 : ℝ)))) =
        (1 / Real.pi) ^ a * Real.Gamma a := by
  rw [← integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
    (a := a) (r := Real.pi) ha Real.pi_pos]
  have h := MeasureTheory.integral_comp_rpow_Ioi
    (g := fun u : ℝ =>
      u ^ (a - 1) * Real.exp (-(Real.pi * u)))
    (p := (-1 : ℝ)) (by norm_num)
  rw [← h]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
  congr 2 <;> ring

/-- The small-end envelope selected by the folded half-plane `sigma >= 1/2`. -/
theorem kernelInverseGammaMoment_quarterRe :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ (-(5 / 4 : ℝ)) * Real.exp (-(Real.pi * t ^ (-1 : ℝ)))) =
        (1 / Real.pi) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) := by
  convert kernelInverseGammaMoment (a := (1 / 4 : ℝ)) (by norm_num) using 1 <;>
    ring

/-- The inverse-exponential envelope is genuinely integrable.  The proof uses
the strictly positive Gamma value, so it cannot accidentally rely on Lean's
default value `0` for the integral of a non-integrable function. -/
theorem integrableOn_kernelInverseGammaMajorant :
    IntegrableOn (fun t : ℝ =>
      t ^ (-(5 / 4 : ℝ)) * Real.exp (-(Real.pi * t ^ (-1 : ℝ))))
      (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [kernelInverseGammaMoment_quarterRe]
  exact mul_ne_zero
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 / Real.pi) _).ne'
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).ne'

/-- Every integer exponential moment used at the large end is genuinely
integrable. -/
theorem integrableOn_kernelPowGammaMajorant (m : Nat) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(Real.pi * t)))
      (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_mul_exp_neg_pi_eq_factorial]
  exact mul_ne_zero
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 / Real.pi) _).ne'
    (by positivity)

/-- The modified theta kernel vanishes at the artificial cut point.  This is
why the open intervals in `WeakFEPair.f_modif` can be assembled without an
uncontrolled endpoint contribution. -/
theorem completedRiemannXiKernel_one :
    completedRiemannXiKernel 1 = 0 := by
  simp [completedRiemannXiKernel, WeakFEPair.f_modif]

/-- The nonnegative kernel-moment integrand is measurable on the positive
axis.  Local integrability of the modified theta kernel supplies the only
non-elementary measurability input. -/
theorem kernelMomentIntegrand_aestronglyMeasurable (sigma : Real) :
    AEStronglyMeasurable
      (fun t : Real =>
        t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖)
      (volume.restrict (Set.Ioi 0)) := by
  have hpow : AEStronglyMeasurable
      (fun t : Real => t ^ (sigma / 2 - 1))
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    exact continuousWithinAt_id.rpow_const (Or.inl ht.ne')
  have hkernel : AEStronglyMeasurable completedRiemannXiKernel
      (volume.restrict (Set.Ioi 0)) :=
    (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_int.aestronglyMeasurable
  exact hpow.mul hkernel.norm

theorem completedRiemannXiKernelMoment_nonneg (sigma : Real) :
    0 <= completedRiemannXiKernelMoment sigma := by
  unfold completedRiemannXiKernelMoment
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _)

/-- On `(0, 1]`, every folded exponent `sigma >= 1/2` is dominated by the
fixed inverse-Gamma envelope with exponent `-5/4`. -/
theorem kernelMomentIntegrand_le_smallMajorant
    {sigma t : Real} (hsigma : 1 / 2 <= sigma) (ht : t ∈ Set.Ioc 0 1) :
    t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖ <=
      completedRiemannXiKernelTailConstant *
        (t ^ (-(5 / 4 : Real)) *
          Real.exp (-(Real.pi * t ^ (-1 : Real)))) := by
  rcases ht.2.eq_or_lt with rfl | htOne
  · rw [completedRiemannXiKernel_one, norm_zero, mul_zero]
    exact mul_nonneg completedRiemannXiKernelTailConstant_nonneg
      (mul_nonneg (Real.rpow_nonneg zero_le_one _) (Real.exp_pos _).le)
  · have htIoo : t ∈ Set.Ioo 0 1 := ⟨ht.1, htOne⟩
    have hkernel := norm_completedRiemannXiKernel_le_inv_exp_of_mem_Ioo htIoo
    have hhalf : 1 / t ^ (1 / 2 : Real) = t ^ (-(1 / 2 : Real)) := by
      rw [one_div, Real.rpow_neg ht.1.le]
    have hinv : 1 / t = t ^ (-1 : Real) := by
      rw [one_div, Real.rpow_neg_one]
    have hpowMul :
        t ^ (sigma / 2 - 1) * (1 / t ^ (1 / 2 : Real)) =
          t ^ (sigma / 2 - 3 / 2) := by
      rw [hhalf, ← Real.rpow_add ht.1]
      congr 1
      ring
    have hpowLe :
        t ^ (sigma / 2 - 3 / 2) <= t ^ (-(5 / 4 : Real)) := by
      apply Real.rpow_le_rpow_of_exponent_ge ht.1 htOne.le
      linarith
    calc
      t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖ <=
          t ^ (sigma / 2 - 1) *
            ((1 / t ^ (1 / 2 : Real)) *
              (completedRiemannXiKernelTailConstant *
                Real.exp (-Real.pi * (1 / t)))) := by
            exact mul_le_mul_of_nonneg_left hkernel
              (Real.rpow_nonneg ht.1.le _)
      _ = completedRiemannXiKernelTailConstant *
          (t ^ (sigma / 2 - 3 / 2) *
            Real.exp (-(Real.pi * t ^ (-1 : Real)))) := by
            rw [← mul_assoc, hpowMul, hinv]
            ring
      _ <= completedRiemannXiKernelTailConstant *
          (t ^ (-(5 / 4 : Real)) *
            Real.exp (-(Real.pi * t ^ (-1 : Real)))) := by
            apply mul_le_mul_of_nonneg_left _
              completedRiemannXiKernelTailConstant_nonneg
            exact mul_le_mul_of_nonneg_right hpowLe (Real.exp_pos _).le

/-- Above one, rounding `sigma / 2` upward to a natural exponent produces an
integer Gamma moment. -/
theorem kernelMomentIntegrand_le_largeMajorant
    {sigma t : Real} (ht : 1 < t) :
    t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖ <=
      completedRiemannXiKernelTailConstant *
        (t ^ (Nat.ceil (sigma / 2)) * Real.exp (-(Real.pi * t))) := by
  have hkernel := norm_completedRiemannXiKernel_le_exp_of_one_lt ht
  have hexponent :
      sigma / 2 - 1 <= (Nat.ceil (sigma / 2) : Real) := by
    linarith [Nat.le_ceil (sigma / 2)]
  have hpow :
      t ^ (sigma / 2 - 1) <= t ^ (Nat.ceil (sigma / 2)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht.le hexponent
  calc
    t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖ <=
        t ^ (sigma / 2 - 1) *
          (completedRiemannXiKernelTailConstant *
            Real.exp (-Real.pi * t)) := by
          exact mul_le_mul_of_nonneg_left hkernel
            (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
    _ <= t ^ (Nat.ceil (sigma / 2)) *
        (completedRiemannXiKernelTailConstant *
          Real.exp (-Real.pi * t)) := by
          exact mul_le_mul_of_nonneg_right hpow
            (mul_nonneg completedRiemannXiKernelTailConstant_nonneg
              (Real.exp_pos _).le)
    _ = completedRiemannXiKernelTailConstant *
        (t ^ (Nat.ceil (sigma / 2)) * Real.exp (-(Real.pi * t))) := by
          ring

theorem kernelMomentIntegrand_integrableOn_small
    {sigma : Real} (hsigma : 1 / 2 <= sigma) :
    IntegrableOn
      (fun t : Real =>
        t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖)
      (Set.Ioc 0 1) := by
  have hmajor : IntegrableOn
      (fun t : Real => completedRiemannXiKernelTailConstant *
        (t ^ (-(5 / 4 : Real)) *
          Real.exp (-(Real.pi * t ^ (-1 : Real)))))
      (Set.Ioc 0 1) := by
    apply IntegrableOn.mono_set
      (integrableOn_kernelInverseGammaMajorant.const_mul
        completedRiemannXiKernelTailConstant)
    exact Set.Ioc_subset_Ioi_self
  apply Integrable.mono'
    hmajor
    ((kernelMomentIntegrand_aestronglyMeasurable sigma).mono_set
      Set.Ioc_subset_Ioi_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))] using
      (kernelMomentIntegrand_le_smallMajorant hsigma ht)

theorem kernelMomentIntegrand_integrableOn_large (sigma : Real) :
    IntegrableOn
      (fun t : Real =>
        t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖)
      (Set.Ioi 1) := by
  have hsubset : Set.Ioi (1 : Real) ⊆ Set.Ioi 0 :=
    Set.Ioi_subset_Ioi (by norm_num)
  have hmajor : IntegrableOn
      (fun t : Real => completedRiemannXiKernelTailConstant *
        (t ^ (Nat.ceil (sigma / 2)) * Real.exp (-(Real.pi * t))))
      (Set.Ioi 1) := by
    apply IntegrableOn.mono_set
      ((integrableOn_kernelPowGammaMajorant
        (Nat.ceil (sigma / 2))).const_mul
          completedRiemannXiKernelTailConstant)
    exact hsubset
  apply Integrable.mono'
    hmajor
    ((kernelMomentIntegrand_aestronglyMeasurable sigma).mono_set hsubset)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
      (norm_nonneg _))] using
        (kernelMomentIntegrand_le_largeMajorant (sigma := sigma) ht)

/-- A folded right-half-plane point has a kernel moment bounded by one fixed
small-end Gamma constant plus one integer Gamma moment.  This is the analytic
growth estimate consumed by the Jensen multiplicity bound. -/
theorem completedRiemannXiKernelMoment_le
    {sigma : Real} (hsigma : 1 / 2 <= sigma) :
    completedRiemannXiKernelMoment sigma <=
      completedRiemannXiKernelTailConstant *
        ((1 / Real.pi) ^ (1 / 4 : Real) * Real.Gamma (1 / 4) +
          (Nat.ceil (sigma / 2) : Real) ^ Nat.ceil (sigma / 2)) := by
  let f : Real -> Real := fun t =>
    t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖
  let small : Real -> Real := fun t =>
    completedRiemannXiKernelTailConstant *
      (t ^ (-(5 / 4 : Real)) *
        Real.exp (-(Real.pi * t ^ (-1 : Real))))
  let m : Nat := Nat.ceil (sigma / 2)
  let large : Real -> Real := fun t =>
    completedRiemannXiKernelTailConstant *
      (t ^ m * Real.exp (-(Real.pi * t)))
  have hfSmall : IntegrableOn f (Set.Ioc 0 1) := by
    simpa only [f] using kernelMomentIntegrand_integrableOn_small hsigma
  have hfLarge : IntegrableOn f (Set.Ioi 1) := by
    simpa only [f] using kernelMomentIntegrand_integrableOn_large sigma
  have hsmallFull : IntegrableOn small (Set.Ioi 0) := by
    simpa only [small] using
      integrableOn_kernelInverseGammaMajorant.const_mul
        completedRiemannXiKernelTailConstant
  have hlargeFull : IntegrableOn large (Set.Ioi 0) := by
    simpa only [large, m] using
      (integrableOn_kernelPowGammaMajorant m).const_mul
        completedRiemannXiKernelTailConstant
  have hsmallRegion : IntegrableOn small (Set.Ioc 0 1) :=
    hsmallFull.mono_set Set.Ioc_subset_Ioi_self
  have hlargeSubset : Set.Ioi (1 : Real) ⊆ Set.Ioi 0 :=
    Set.Ioi_subset_Ioi (by norm_num)
  have hlargeRegion : IntegrableOn large (Set.Ioi 1) :=
    hlargeFull.mono_set hlargeSubset
  have hsmallIntegral :
      (∫ t : Real in Set.Ioc 0 1, f t) <=
        completedRiemannXiKernelTailConstant *
          ((1 / Real.pi) ^ (1 / 4 : Real) * Real.Gamma (1 / 4)) := by
    calc
      (∫ t : Real in Set.Ioc 0 1, f t) <=
          ∫ t : Real in Set.Ioc 0 1, small t := by
            apply setIntegral_mono_on hfSmall hsmallRegion measurableSet_Ioc
            intro t ht
            exact kernelMomentIntegrand_le_smallMajorant hsigma ht
      _ <= ∫ t : Real in Set.Ioi 0, small t := by
            apply setIntegral_mono_set hsmallFull
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact mul_nonneg completedRiemannXiKernelTailConstant_nonneg
                (mul_nonneg (Real.rpow_nonneg ht.le _)
                  (Real.exp_pos _).le)
            · exact Set.Ioc_subset_Ioi_self.eventuallyLE
      _ = completedRiemannXiKernelTailConstant *
          ((1 / Real.pi) ^ (1 / 4 : Real) * Real.Gamma (1 / 4)) := by
            simp only [small, integral_const_mul,
              kernelInverseGammaMoment_quarterRe]
  have hlargeIntegral :
      (∫ t : Real in Set.Ioi 1, f t) <=
        completedRiemannXiKernelTailConstant * (m : Real) ^ m := by
    calc
      (∫ t : Real in Set.Ioi 1, f t) <=
          ∫ t : Real in Set.Ioi 1, large t := by
            apply setIntegral_mono_on hfLarge hlargeRegion measurableSet_Ioi
            intro t ht
            simpa only [large, m] using
              (kernelMomentIntegrand_le_largeMajorant (sigma := sigma) ht)
      _ <= ∫ t : Real in Set.Ioi 0, large t := by
            apply setIntegral_mono_set hlargeFull
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact mul_nonneg completedRiemannXiKernelTailConstant_nonneg
                (mul_nonneg (pow_nonneg ht.le _)
                  (Real.exp_pos _).le)
            · exact hlargeSubset.eventuallyLE
      _ = completedRiemannXiKernelTailConstant *
          (∫ t : Real in Set.Ioi 0,
            t ^ m * Real.exp (-(Real.pi * t))) := by
            simp only [large, integral_const_mul]
      _ <= completedRiemannXiKernelTailConstant * (m : Real) ^ m := by
            exact mul_le_mul_of_nonneg_left
              (integral_pow_mul_exp_neg_pi_le_pow_self m)
              completedRiemannXiKernelTailConstant_nonneg
  unfold completedRiemannXiKernelMoment
  change (∫ t : Real in Set.Ioi 0, f t) <= _
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : Real) <= 1 by norm_num)]
  rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    hfSmall hfLarge]
  have hsum := add_le_add hsmallIntegral hlargeIntegral
  dsimp only [m] at hsum ⊢
  linarith

end C1XiGrowth
end Source
end ConnesWeilRH
