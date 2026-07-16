/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The CCM24 multiplicative Haar carrier

CCM24 first sends an even function on the additive real line to the
multiplicative half-line by the half-density map

`w_infinity(f)(rho) = rho^(1/2) * f(rho)`.

The multiplicative Fourier transform then uses Haar measure `d rho / rho`.
This module constructs that Haar `L2` carrier independently of the
Hardy--Titchmarsh operator: its measure is the pushforward of Lebesgue measure
under `t -> exp t`.  Consequently logarithmic pullback is a genuine linear
isometry equivalence, with an explicit inverse through `log`.

This is the carrier layer only.  Identifying the additive even Fourier
transform with `ccm24ArchimedeanHardyTitchmarsh` still requires the independent
Mellin--Fourier functional equation.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set Filter Asymptotics Topology
open scoped FourierTransform

/-- The actual even additive `L2(R)` carrier, realized as the fixed space of
reflection `f(x) -> f(-x)`. -/
noncomputable def ccm24EvenAdditiveClosedSubspace :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 where
  toSubmodule :=
    (ccm24LogSpectralReflection.toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2).ker
  isClosed' :=
    (ccm24LogSpectralReflection.toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2).isClosed_ker

/-- The Hilbert carrier `L2(R)^ev` from CCM24. -/
noncomputable abbrev ccm24EvenAdditiveL2 :=
  ccm24EvenAdditiveClosedSubspace.toSubmodule

theorem mem_ccm24EvenAdditiveClosedSubspace_iff
    (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24EvenAdditiveClosedSubspace ↔
      ccm24LogSpectralReflection u = u := by
  change
    ccm24LogSpectralReflection u - u = 0 ↔
      ccm24LogSpectralReflection u = u
  exact sub_eq_zero

/-- Membership in the fixed-point carrier is precisely almost-everywhere
evenness of the represented `L2` function. -/
theorem mem_ccm24EvenAdditiveClosedSubspace_iff_ae_even
    (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24EvenAdditiveClosedSubspace ↔
      ∀ᵐ x ∂volume, u (-x) = u x := by
  rw [mem_ccm24EvenAdditiveClosedSubspace_iff]
  constructor
  · intro hu
    rw [Lp.ext_iff] at hu
    filter_upwards [ccm24LogSpectralReflectionEquiv_coeFn u, hu] with
      x href heq
    rw [← heq, href]
  · intro hu
    rw [Lp.ext_iff]
    filter_upwards [ccm24LogSpectralReflectionEquiv_coeFn u, hu] with
      x href heven
    rw [href, heven]

/-- An almost-everywhere even nonnegative density has twice its positive
half-line mass. -/
theorem lintegral_eq_two_mul_setLIntegral_Ioi_of_ae_even
    (v : ℝ → ENNReal)
    (heven : ∀ᵐ x ∂volume, v (-x) = v x) :
    (∫⁻ x, v x ∂volume) =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume := by
  have hneg :=
    (Measure.measurePreserving_neg volume).setLIntegral_comp_preimage_emb
      measurableEmbedding_neg v (Set.Ioi (0 : ℝ))
  have hpreimage :
      (fun x : ℝ => -x) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio 0 := by
    ext x
    simp
  rw [hpreimage] at hneg
  have hevenIio := ae_restrict_of_ae (s := Set.Iio (0 : ℝ)) heven
  have hevenIioSymm :
      ∀ᵐ x ∂volume.restrict (Set.Iio (0 : ℝ)), v x = v (-x) := by
    filter_upwards [hevenIio] with x hx
    exact hx.symm
  have hhalves :
      (∫⁻ x in Set.Iio (0 : ℝ), v x ∂volume) =
        ∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume := by
    calc
      (∫⁻ x in Set.Iio (0 : ℝ), v x ∂volume) =
          ∫⁻ x in Set.Iio (0 : ℝ), v (-x) ∂volume :=
        lintegral_congr_ae hevenIioSymm
      _ = ∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume := hneg
  have hIic :
      (∫⁻ x in Set.Iic (0 : ℝ), v x ∂volume) =
        ∫⁻ x in Set.Iio (0 : ℝ), v x ∂volume := by
    have hset : Set.Iic (0 : ℝ) = Set.Iio 0 ∪ {0} := by
      ext x
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
      exact le_iff_lt_or_eq
    rw [hset, lintegral_union (measurableSet_singleton (0 : ℝ))]
    · simp
    · exact Set.disjoint_singleton_right.mpr (by simp)
  have hsplit := lintegral_add_compl (μ := volume) v (measurableSet_Ioi :
    MeasurableSet (Set.Ioi (0 : ℝ)))
  rw [Set.compl_Ioi, hIic, hhalves] at hsplit
  calc
    (∫⁻ x, v x ∂volume) =
        (∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume) +
          ∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume := hsplit.symm
    _ = 2 * ∫⁻ x in Set.Ioi (0 : ℝ), v x ∂volume := by
      rw [two_mul]

/-- Change of variables `rho = exp t` for a nonnegative density. -/
theorem lintegral_exp_mul_eq_setLIntegral_Ioi
    (v : ℝ → ENNReal) :
    (∫⁻ t, ENNReal.ofReal (Real.exp t) * v (Real.exp t) ∂volume) =
      ∫⁻ rho in Set.Ioi (0 : ℝ), v rho ∂volume := by
  have hchange :=
    lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (f := Real.exp) (f' := Real.exp) (s := Set.univ)
      MeasurableSet.univ
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
      (Real.exp_monotone.monotoneOn Set.univ) v
  rw [Set.image_univ, Real.range_exp] at hchange
  simpa using hchange.symm

/-- The normalized log half-density has exactly the full mass of an even
additive density.  This is the squared-norm identity behind the factor
`sqrt 2 * exp(t / 2)` in the unitary realization of `w_infinity`. -/
theorem lintegral_normalized_log_halfDensity_of_ae_even
    (v : ℝ → ENNReal)
    (heven : ∀ᵐ x ∂volume, v (-x) = v x) :
    (∫⁻ t, 2 * (ENNReal.ofReal (Real.exp t) * v (Real.exp t)) ∂volume) =
      ∫⁻ x, v x ∂volume := by
  rw [lintegral_const_mul' 2
    (fun t => ENNReal.ofReal (Real.exp t) * v (Real.exp t)) (by simp)]
  rw [lintegral_exp_mul_eq_setLIntegral_Ioi]
  exact (lintegral_eq_two_mul_setLIntegral_Ioi_of_ae_even v heven).symm

/-- Mathlib's canonical strongly-measurable representative of an element of
the even additive `L2` carrier. -/
noncomputable def ccm24EvenAdditiveRepresentative
    (u : ccm24EvenAdditiveL2) : ℝ → ℂ :=
  (Lp.aestronglyMeasurable (u : cc20GlobalLogCrossingL2)).mk
    (u : cc20GlobalLogCrossingL2)

theorem stronglyMeasurable_ccm24EvenAdditiveRepresentative
    (u : ccm24EvenAdditiveL2) :
    StronglyMeasurable (ccm24EvenAdditiveRepresentative u) :=
  (Lp.aestronglyMeasurable
    (u : cc20GlobalLogCrossingL2)).stronglyMeasurable_mk

theorem ccm24EvenAdditiveRepresentative_ae_eq
    (u : ccm24EvenAdditiveL2) :
    ((u : cc20GlobalLogCrossingL2) : ℝ → ℂ) =ᵐ[volume]
      ccm24EvenAdditiveRepresentative u :=
  (Lp.aestronglyMeasurable
    (u : cc20GlobalLogCrossingL2)).ae_eq_mk

/-- The canonical representative remains even almost everywhere. -/
theorem ccm24EvenAdditiveRepresentative_ae_even
    (u : ccm24EvenAdditiveL2) :
    ∀ᵐ x ∂volume,
      ccm24EvenAdditiveRepresentative u (-x) =
        ccm24EvenAdditiveRepresentative u x := by
  have hrep := ccm24EvenAdditiveRepresentative_ae_eq u
  have hrepNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hrep
  have heven :=
    (mem_ccm24EvenAdditiveClosedSubspace_iff_ae_even
      (u : cc20GlobalLogCrossingL2)).1 u.property
  filter_upwards [hrep, hrepNeg, heven] with x hrepAt hrepNegAt hevenAt
  simp only [Function.comp_apply] at hrepNegAt
  rw [← hrepNegAt, hevenAt, hrepAt]

/-- The normalized common-log half-density transform on a representative
function. -/
noncomputable def ccm24NormalizedLogHalfDensityFunction
    (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
    f (Real.exp t)

/-- The normalized common-log half-density attached to an actual even
additive `L2` vector. -/
noncomputable def ccm24NormalizedLogHalfDensityRaw
    (u : ccm24EvenAdditiveL2) : ℝ → ℂ :=
  ccm24NormalizedLogHalfDensityFunction
    (ccm24EvenAdditiveRepresentative u)

theorem stronglyMeasurable_ccm24NormalizedLogHalfDensityRaw
    (u : ccm24EvenAdditiveL2) :
    StronglyMeasurable (ccm24NormalizedLogHalfDensityRaw u) := by
  apply StronglyMeasurable.smul
  · exact
      ((Real.continuous_sqrt.comp continuous_const).mul
        (Real.continuous_exp.comp (continuous_id.div_const 2))).measurable
        |>.stronglyMeasurable
  · exact
      (stronglyMeasurable_ccm24EvenAdditiveRepresentative u).comp_measurable
        Real.continuous_exp.measurable

/-- Pointwise squared extended norm of the normalized half-density. -/
theorem ccm24NormalizedLogHalfDensityRaw_enorm_sq
    (u : ccm24EvenAdditiveL2) (t : ℝ) :
    ‖ccm24NormalizedLogHalfDensityRaw u t‖ₑ ^ (2 : ℝ) =
      2 * (ENNReal.ofReal (Real.exp t) *
        (‖ccm24EvenAdditiveRepresentative u (Real.exp t)‖ₑ ^ (2 : ℝ))) := by
  have hfactor_nonneg :
      0 ≤ Real.sqrt 2 * Real.exp (t / 2) :=
    mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le
  have hfactor_sq :
      (Real.sqrt 2 * Real.exp (t / 2)) ^ 2 = 2 * Real.exp t := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), pow_two, ← Real.exp_add]
    congr 2
    ring
  have hfactor_enorm :
      ‖Real.sqrt 2 * Real.exp (t / 2)‖ₑ =
        ENNReal.ofReal (Real.sqrt 2 * Real.exp (t / 2)) := by
    rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg hfactor_nonneg,
      ENNReal.ofReal_eq_coe_nnreal hfactor_nonneg]
  simp only [ccm24NormalizedLogHalfDensityRaw,
    ccm24NormalizedLogHalfDensityFunction, ENNReal.rpow_two,
    enorm_smul, mul_pow]
  rw [hfactor_enorm]
  rw [← ENNReal.ofReal_pow (by positivity), hfactor_sq,
    ENNReal.ofReal_mul (by positivity)]
  norm_num
  ring

/-- A strongly measurable representative which vanishes almost everywhere
still vanishes after normalized half-density transport.  This is proved by
the squared-mass identity, not by assuming that `exp` preserves arbitrary
Lebesgue null sets definitionally. -/
theorem ccm24NormalizedLogHalfDensityFunction_ae_zero
    (f : ℝ → ℂ) (hf : StronglyMeasurable f)
    (hzero : f =ᵐ[volume] 0) :
    ccm24NormalizedLogHalfDensityFunction f =ᵐ[volume] 0 := by
  have hzeroNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hzero
  have hnormEven :
      ∀ᵐ x ∂volume, ‖f (-x)‖ₑ ^ (2 : ℕ) = ‖f x‖ₑ ^ (2 : ℕ) := by
    filter_upwards [hzero, hzeroNeg] with x hx hxNeg
    simp only [Function.comp_apply, Pi.zero_apply] at hxNeg
    simp only [hx, hxNeg, Pi.zero_apply, enorm_zero]
  have hmass := lintegral_normalized_log_halfDensity_of_ae_even
    (fun x => ‖f x‖ₑ ^ (2 : ℕ)) hnormEven
  have hsourceZero :
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
    calc
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂volume) =
          ∫⁻ _x : ℝ, (0 : ENNReal) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [hzero] with x hx
        rw [hx]
        simp
      _ = 0 := by simp
  have htargetIntegral :
      (∫⁻ t, ‖ccm24NormalizedLogHalfDensityFunction f t‖ₑ ^ (2 : ℕ)
        ∂volume) = 0 := by
    calc
      (∫⁻ t, ‖ccm24NormalizedLogHalfDensityFunction f t‖ₑ ^ (2 : ℕ)
        ∂volume) =
          ∫⁻ t, 2 * (ENNReal.ofReal (Real.exp t) *
            (‖f (Real.exp t)‖ₑ ^ (2 : ℕ))) ∂volume := by
        apply lintegral_congr
        intro t
        -- The scalar calculation is independent of the representative.
        simp only [ccm24NormalizedLogHalfDensityFunction]
        have hfactor_nonneg :
            0 ≤ Real.sqrt 2 * Real.exp (t / 2) :=
          mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le
        have hfactor_sq :
            (Real.sqrt 2 * Real.exp (t / 2)) ^ 2 = 2 * Real.exp t := by
          rw [mul_pow, Real.sq_sqrt (by norm_num), pow_two, ← Real.exp_add]
          congr 2
          ring
        have hfactor_enorm :
            ‖Real.sqrt 2 * Real.exp (t / 2)‖ₑ =
              ENNReal.ofReal (Real.sqrt 2 * Real.exp (t / 2)) := by
          rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg hfactor_nonneg,
            ENNReal.ofReal_eq_coe_nnreal hfactor_nonneg]
        simp only [enorm_smul, mul_pow]
        rw [hfactor_enorm]
        rw [← ENNReal.ofReal_pow (by positivity), hfactor_sq,
          ENNReal.ofReal_mul (by positivity)]
        norm_num
        ring
      _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂volume := hmass
      _ = 0 := hsourceZero
  have hstrong :
      AEStronglyMeasurable (ccm24NormalizedLogHalfDensityFunction f) volume := by
    apply StronglyMeasurable.aestronglyMeasurable
    apply StronglyMeasurable.smul
    · exact
        ((Real.continuous_sqrt.comp continuous_const).mul
          (Real.continuous_exp.comp (continuous_id.div_const 2))).measurable
          |>.stronglyMeasurable
    · exact hf.comp_measurable Real.continuous_exp.measurable
  have help :
      eLpNorm (ccm24NormalizedLogHalfDensityFunction f) 2 volume = 0 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)]
    norm_num
    rw [htargetIntegral]
  exact (eLpNorm_eq_zero_iff hstrong (by norm_num)).1 help

theorem eLpNorm_ccm24NormalizedLogHalfDensityRaw
    (u : ccm24EvenAdditiveL2) :
    eLpNorm (ccm24NormalizedLogHalfDensityRaw u) 2 volume =
      eLpNorm (u : ℝ → ℂ) 2 volume := by
  have hrepEven := ccm24EvenAdditiveRepresentative_ae_even u
  have hnormEven :
      ∀ᵐ x ∂volume,
        ‖ccm24EvenAdditiveRepresentative u (-x)‖ₑ ^ (2 : ℕ) =
          ‖ccm24EvenAdditiveRepresentative u x‖ₑ ^ (2 : ℕ) := by
    filter_upwards [hrepEven] with x hx
    rw [hx]
  have hmass := lintegral_normalized_log_halfDensity_of_ae_even
    (fun x => ‖ccm24EvenAdditiveRepresentative u x‖ₑ ^ (2 : ℕ))
    hnormEven
  have hrawIntegral :
      (∫⁻ t, ‖ccm24NormalizedLogHalfDensityRaw u t‖ₑ ^ (2 : ℕ)
          ∂volume) =
        ∫⁻ x, ‖ccm24EvenAdditiveRepresentative u x‖ₑ ^ (2 : ℕ)
          ∂volume := by
    calc
      (∫⁻ t, ‖ccm24NormalizedLogHalfDensityRaw u t‖ₑ ^ (2 : ℕ)
          ∂volume) =
          ∫⁻ t, 2 * (ENNReal.ofReal (Real.exp t) *
            (‖ccm24EvenAdditiveRepresentative u (Real.exp t)‖ₑ ^
              (2 : ℕ))) ∂volume := by
        apply lintegral_congr
        intro t
        simpa only [ENNReal.rpow_two] using
          ccm24NormalizedLogHalfDensityRaw_enorm_sq u t
      _ = ∫⁻ x, ‖ccm24EvenAdditiveRepresentative u x‖ₑ ^ (2 : ℕ)
          ∂volume := hmass
  calc
    eLpNorm (ccm24NormalizedLogHalfDensityRaw u) 2 volume =
        eLpNorm (ccm24EvenAdditiveRepresentative u) 2 volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num)]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num)]
      norm_num
      exact congrArg (fun z : ENNReal => z ^ (1 / 2 : ℝ)) hrawIntegral
    _ = eLpNorm (u : ℝ → ℂ) 2 volume :=
      eLpNorm_congr_ae (ccm24EvenAdditiveRepresentative_ae_eq u).symm

theorem memLp_ccm24NormalizedLogHalfDensityRaw
    (u : ccm24EvenAdditiveL2) :
    MemLp (ccm24NormalizedLogHalfDensityRaw u) 2 volume := by
  constructor
  · exact (stronglyMeasurable_ccm24NormalizedLogHalfDensityRaw u).aestronglyMeasurable
  · rw [eLpNorm_ccm24NormalizedLogHalfDensityRaw]
    exact (Lp.memLp (u : cc20GlobalLogCrossingL2)).2

/-- The normalized half-density as an actual vector in the common
logarithmic `L2` carrier. -/
noncomputable def ccm24EvenToLogHalfDensity
    (u : ccm24EvenAdditiveL2) : cc20GlobalLogCrossingL2 :=
  (memLp_ccm24NormalizedLogHalfDensityRaw u).toLp
    (ccm24NormalizedLogHalfDensityRaw u)

theorem ccm24EvenToLogHalfDensity_coeFn
    (u : ccm24EvenAdditiveL2) :
    (ccm24EvenToLogHalfDensity u : ℝ → ℂ) =ᵐ[volume]
      ccm24NormalizedLogHalfDensityRaw u :=
  (memLp_ccm24NormalizedLogHalfDensityRaw u).coeFn_toLp

/-- The normalized half-density respects almost-everywhere equality of
strongly measurable source representatives. -/
theorem ccm24NormalizedLogHalfDensityFunction_congr_ae
    {f g : ℝ → ℂ}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfg : f =ᵐ[volume] g) :
    ccm24NormalizedLogHalfDensityFunction f =ᵐ[volume]
      ccm24NormalizedLogHalfDensityFunction g := by
  have hzero : (fun x => f x - g x) =ᵐ[volume] 0 := by
    filter_upwards [hfg] with x hx
    rw [hx, sub_self]
    simp only [Pi.zero_apply]
  have htransport := ccm24NormalizedLogHalfDensityFunction_ae_zero
    (fun x => f x - g x) (hf.sub hg) hzero
  filter_upwards [htransport] with t ht
  rw [← sub_eq_zero]
  simpa only [ccm24NormalizedLogHalfDensityFunction, smul_sub] using ht

/-- The explicit normalized half-density preserves the full even `L2`
norm. -/
theorem norm_ccm24EvenToLogHalfDensity
    (u : ccm24EvenAdditiveL2) :
    ‖ccm24EvenToLogHalfDensity u‖ = ‖u‖ := by
  change
    ‖ccm24EvenToLogHalfDensity u‖ =
      ‖(u : cc20GlobalLogCrossingL2)‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (ccm24EvenToLogHalfDensity_coeFn u)]
  rw [eLpNorm_ccm24NormalizedLogHalfDensityRaw]

theorem ccm24EvenAdditiveRepresentative_add_defect_ae_zero
    (u v : ccm24EvenAdditiveL2) :
    (fun x =>
      ccm24EvenAdditiveRepresentative (u + v) x -
        ccm24EvenAdditiveRepresentative u x -
        ccm24EvenAdditiveRepresentative v x) =ᵐ[volume] 0 := by
  have hsum := ccm24EvenAdditiveRepresentative_ae_eq (u + v)
  have hu := ccm24EvenAdditiveRepresentative_ae_eq u
  have hv := ccm24EvenAdditiveRepresentative_ae_eq v
  have hadd := Lp.coeFn_add
    (u : cc20GlobalLogCrossingL2) (v : cc20GlobalLogCrossingL2)
  filter_upwards [hsum, hu, hv, hadd] with x hsumAt huAt hvAt haddAt
  change
    (((u + v : ccm24EvenAdditiveL2) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x =
      (((u : cc20GlobalLogCrossingL2) : ℝ → ℂ) x +
        ((v : cc20GlobalLogCrossingL2) : ℝ → ℂ) x) at haddAt
  rw [← hsumAt, haddAt, huAt, hvAt]
  simp

theorem ccm24NormalizedLogHalfDensityRaw_add_ae
    (u v : ccm24EvenAdditiveL2) :
    ccm24NormalizedLogHalfDensityRaw (u + v) =ᵐ[volume]
      fun t => ccm24NormalizedLogHalfDensityRaw u t +
        ccm24NormalizedLogHalfDensityRaw v t := by
  let defect : ℝ → ℂ := fun x =>
    ccm24EvenAdditiveRepresentative (u + v) x -
      ccm24EvenAdditiveRepresentative u x -
      ccm24EvenAdditiveRepresentative v x
  have hdefectStrong : StronglyMeasurable defect :=
    ((stronglyMeasurable_ccm24EvenAdditiveRepresentative (u + v)).sub
      (stronglyMeasurable_ccm24EvenAdditiveRepresentative u)).sub
        (stronglyMeasurable_ccm24EvenAdditiveRepresentative v)
  have hdefectZero : defect =ᵐ[volume] 0 :=
    ccm24EvenAdditiveRepresentative_add_defect_ae_zero u v
  have htransportZero :=
    ccm24NormalizedLogHalfDensityFunction_ae_zero
      defect hdefectStrong hdefectZero
  filter_upwards [htransportZero] with t ht
  change
    (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
        ccm24EvenAdditiveRepresentative (u + v) (Real.exp t) =
      (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          ccm24EvenAdditiveRepresentative u (Real.exp t) +
        (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          ccm24EvenAdditiveRepresentative v (Real.exp t)
  apply sub_eq_zero.mp
  simp only [defect, ccm24NormalizedLogHalfDensityFunction,
    Pi.zero_apply, smul_sub, sub_sub] at ht
  rw [smul_add] at ht
  exact ht

theorem ccm24EvenToLogHalfDensity_add
    (u v : ccm24EvenAdditiveL2) :
    ccm24EvenToLogHalfDensity (u + v) =
      ccm24EvenToLogHalfDensity u + ccm24EvenToLogHalfDensity v := by
  rw [Lp.ext_iff]
  filter_upwards
    [ccm24EvenToLogHalfDensity_coeFn (u + v),
      ccm24EvenToLogHalfDensity_coeFn u,
      ccm24EvenToLogHalfDensity_coeFn v,
      Lp.coeFn_add (ccm24EvenToLogHalfDensity u)
        (ccm24EvenToLogHalfDensity v),
      ccm24NormalizedLogHalfDensityRaw_add_ae u v] with
      t hsum hu hv hadd hraw
  rw [hsum, hadd]
  simp only [Pi.add_apply]
  rw [hu, hv]
  exact hraw

theorem ccm24EvenAdditiveRepresentative_smul_defect_ae_zero
    (c : ℂ) (u : ccm24EvenAdditiveL2) :
    (fun x =>
      ccm24EvenAdditiveRepresentative (c • u) x -
        c • ccm24EvenAdditiveRepresentative u x) =ᵐ[volume] 0 := by
  have hcu := ccm24EvenAdditiveRepresentative_ae_eq (c • u)
  have hu := ccm24EvenAdditiveRepresentative_ae_eq u
  have hsmul := Lp.coeFn_smul c (u : cc20GlobalLogCrossingL2)
  filter_upwards [hcu, hu, hsmul] with x hcuAt huAt hsmulAt
  change
    (((c • u : ccm24EvenAdditiveL2) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x =
      c • ((u : cc20GlobalLogCrossingL2) : ℝ → ℂ) x at hsmulAt
  rw [← hcuAt, hsmulAt, huAt]
  simp

theorem ccm24NormalizedLogHalfDensityRaw_smul_ae
    (c : ℂ) (u : ccm24EvenAdditiveL2) :
    ccm24NormalizedLogHalfDensityRaw (c • u) =ᵐ[volume]
      fun t => c • ccm24NormalizedLogHalfDensityRaw u t := by
  let defect : ℝ → ℂ := fun x =>
    ccm24EvenAdditiveRepresentative (c • u) x -
      c • ccm24EvenAdditiveRepresentative u x
  have hdefectStrong : StronglyMeasurable defect :=
    (stronglyMeasurable_ccm24EvenAdditiveRepresentative (c • u)).sub
      ((stronglyMeasurable_const.smul
        (stronglyMeasurable_ccm24EvenAdditiveRepresentative u)))
  have hdefectZero : defect =ᵐ[volume] 0 :=
    ccm24EvenAdditiveRepresentative_smul_defect_ae_zero c u
  have htransportZero :=
    ccm24NormalizedLogHalfDensityFunction_ae_zero
      defect hdefectStrong hdefectZero
  filter_upwards [htransportZero] with t ht
  change
    (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
        ccm24EvenAdditiveRepresentative (c • u) (Real.exp t) =
      c • ((Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
        ccm24EvenAdditiveRepresentative u (Real.exp t))
  apply sub_eq_zero.mp
  simp only [defect, ccm24NormalizedLogHalfDensityFunction,
    Pi.zero_apply, smul_sub] at ht
  calc
    (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          ccm24EvenAdditiveRepresentative (c • u) (Real.exp t) -
        c • ((Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          ccm24EvenAdditiveRepresentative u (Real.exp t)) =
      (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          ccm24EvenAdditiveRepresentative (c • u) (Real.exp t) -
        (Real.sqrt 2 * Real.exp (t / 2) : ℝ) •
          (c • ccm24EvenAdditiveRepresentative u (Real.exp t)) := by
        rw [smul_comm]
    _ = 0 := ht

theorem ccm24EvenToLogHalfDensity_smul
    (c : ℂ) (u : ccm24EvenAdditiveL2) :
    ccm24EvenToLogHalfDensity (c • u) =
      c • ccm24EvenToLogHalfDensity u := by
  rw [Lp.ext_iff]
  filter_upwards
    [ccm24EvenToLogHalfDensity_coeFn (c • u),
      ccm24EvenToLogHalfDensity_coeFn u,
      Lp.coeFn_smul c (ccm24EvenToLogHalfDensity u),
      ccm24NormalizedLogHalfDensityRaw_smul_ae c u] with
      t hcu hu hsmul hraw
  rw [hcu, hsmul]
  simp only [Pi.smul_apply]
  rw [hu]
  exact hraw

/-- The normalized archimedean half-density as a genuine complex-linear
isometry from `L2(R)^ev` into the common logarithmic carrier. -/
noncomputable def ccm24EvenToLogHalfDensityLinearIsometry :
    ccm24EvenAdditiveL2 →ₗᵢ[ℂ] cc20GlobalLogCrossingL2 where
  toFun := ccm24EvenToLogHalfDensity
  map_add' := ccm24EvenToLogHalfDensity_add
  map_smul' := ccm24EvenToLogHalfDensity_smul
  norm_map' := norm_ccm24EvenToLogHalfDensity

/-- Canonical strongly-measurable representative of a common-log `L2`
vector. -/
noncomputable def ccm24LogRepresentative
    (u : cc20GlobalLogCrossingL2) : ℝ → ℂ :=
  (Lp.aestronglyMeasurable u).mk u

theorem stronglyMeasurable_ccm24LogRepresentative
    (u : cc20GlobalLogCrossingL2) :
    StronglyMeasurable (ccm24LogRepresentative u) :=
  (Lp.aestronglyMeasurable u).stronglyMeasurable_mk

theorem ccm24LogRepresentative_ae_eq
    (u : cc20GlobalLogCrossingL2) :
    (u : ℝ → ℂ) =ᵐ[volume] ccm24LogRepresentative u :=
  (Lp.aestronglyMeasurable u).ae_eq_mk

/-- Explicit inverse normalized half-density on the additive real line. -/
noncomputable def ccm24LogToEvenHalfDensityRaw
    (u : cc20GlobalLogCrossingL2) (x : ℝ) : ℂ :=
  if x = 0 then 0 else
    ((1 / Real.sqrt 2) * |x| ^ (-1 / 2 : ℝ)) •
      ccm24LogRepresentative u (Real.log |x|)

theorem measurable_ccm24LogToEvenHalfDensityRaw
    (u : cc20GlobalLogCrossingL2) :
    Measurable (ccm24LogToEvenHalfDensityRaw u) := by
  have hpow : Measurable (fun x : ℝ => |x| ^ (-1 / 2 : ℝ)) := by
    apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
    apply ContinuousOn.rpow_const continuous_abs.continuousOn
    intro x hx
    apply Or.inl
    exact abs_ne_zero.mpr (by simpa using hx)
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  apply Measurable.smul
  · apply Measurable.mul measurable_const
    exact hpow
  · exact
      (stronglyMeasurable_ccm24LogRepresentative u).measurable.comp
        (Real.measurable_log.comp continuous_abs.measurable)

theorem ccm24LogToEvenHalfDensityRaw_even
    (u : cc20GlobalLogCrossingL2) (x : ℝ) :
    ccm24LogToEvenHalfDensityRaw u (-x) =
      ccm24LogToEvenHalfDensityRaw u x := by
  simp [ccm24LogToEvenHalfDensityRaw]

/-- Positive-coordinate readback of the explicit inverse. -/
theorem ccm24LogToEvenHalfDensityRaw_exp
    (u : cc20GlobalLogCrossingL2) (t : ℝ) :
    ccm24LogToEvenHalfDensityRaw u (Real.exp t) =
      ((1 / Real.sqrt 2) * Real.exp (-t / 2)) •
        ccm24LogRepresentative u t := by
  simp only [ccm24LogToEvenHalfDensityRaw, Real.exp_ne_zero, if_false,
    abs_of_pos (Real.exp_pos t), Real.log_exp]
  congr 1
  rw [Real.rpow_def_of_pos (Real.exp_pos t)]
  rw [Real.log_exp]
  congr 2
  ring

theorem ccm24LogToEvenHalfDensityRaw_exp_enorm_sq
    (u : cc20GlobalLogCrossingL2) (t : ℝ) :
    2 * (ENNReal.ofReal (Real.exp t) *
      (‖ccm24LogToEvenHalfDensityRaw u (Real.exp t)‖ₑ ^ (2 : ℕ))) =
        ‖ccm24LogRepresentative u t‖ₑ ^ (2 : ℕ) := by
  let factor : ℝ := (1 / Real.sqrt 2) * Real.exp (-t / 2)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hfactor_nonneg : 0 ≤ factor :=
    mul_nonneg (div_nonneg (by norm_num) hsqrt_pos.le)
      (Real.exp_pos _).le
  have hcoef_real : 2 * Real.exp t * factor ^ 2 = 1 := by
    dsimp [factor]
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num),
      pow_two, ← Real.exp_add]
    field_simp [hsqrt_pos.ne']
    ring_nf
    rw [← Real.exp_add]
    simp
  have hfactor_enorm : ‖factor‖ₑ = ENNReal.ofReal factor := by
    rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg hfactor_nonneg,
      ENNReal.ofReal_eq_coe_nnreal hfactor_nonneg]
  have hcoef_ennreal :
      (2 : ENNReal) * ENNReal.ofReal (Real.exp t) *
          (ENNReal.ofReal factor) ^ 2 = 1 := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.exp_pos t).le)]
    rw [hcoef_real]
    simp
  rw [ccm24LogToEvenHalfDensityRaw_exp]
  change
    2 * (ENNReal.ofReal (Real.exp t) *
      (‖factor • ccm24LogRepresentative u t‖ₑ ^ (2 : ℕ))) = _
  simp only [enorm_smul, mul_pow]
  rw [hfactor_enorm]
  calc
    2 * (ENNReal.ofReal (Real.exp t) *
        ((ENNReal.ofReal factor) ^ 2 *
          ‖ccm24LogRepresentative u t‖ₑ ^ 2)) =
      ((2 : ENNReal) * ENNReal.ofReal (Real.exp t) *
        (ENNReal.ofReal factor) ^ 2) *
          ‖ccm24LogRepresentative u t‖ₑ ^ 2 := by ring
    _ = ‖ccm24LogRepresentative u t‖ₑ ^ 2 := by
      rw [hcoef_ennreal, one_mul]

theorem eLpNorm_ccm24LogToEvenHalfDensityRaw
    (u : cc20GlobalLogCrossingL2) :
    eLpNorm (ccm24LogToEvenHalfDensityRaw u) 2 volume =
      eLpNorm (u : ℝ → ℂ) 2 volume := by
  have hevenNorm :
      ∀ᵐ x ∂volume,
        ‖ccm24LogToEvenHalfDensityRaw u (-x)‖ₑ ^ (2 : ℕ) =
          ‖ccm24LogToEvenHalfDensityRaw u x‖ₑ ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun x => by
      rw [ccm24LogToEvenHalfDensityRaw_even]
  have hfull := lintegral_eq_two_mul_setLIntegral_Ioi_of_ae_even
    (fun x => ‖ccm24LogToEvenHalfDensityRaw u x‖ₑ ^ (2 : ℕ))
    hevenNorm
  have hchange := lintegral_exp_mul_eq_setLIntegral_Ioi
    (fun x => ‖ccm24LogToEvenHalfDensityRaw u x‖ₑ ^ (2 : ℕ))
  rw [← hchange] at hfull
  have hrawIntegral :
      (∫⁻ x, ‖ccm24LogToEvenHalfDensityRaw u x‖ₑ ^ (2 : ℕ)
        ∂volume) =
        ∫⁻ t, ‖ccm24LogRepresentative u t‖ₑ ^ (2 : ℕ) ∂volume := by
    calc
      (∫⁻ x, ‖ccm24LogToEvenHalfDensityRaw u x‖ₑ ^ (2 : ℕ)
        ∂volume) =
          2 * ∫⁻ t, ENNReal.ofReal (Real.exp t) *
            ‖ccm24LogToEvenHalfDensityRaw u (Real.exp t)‖ₑ ^ (2 : ℕ)
              ∂volume := hfull
      _ = ∫⁻ t, 2 * (ENNReal.ofReal (Real.exp t) *
            ‖ccm24LogToEvenHalfDensityRaw u (Real.exp t)‖ₑ ^ (2 : ℕ))
              ∂volume := by
        rw [lintegral_const_mul' 2 _ (by simp)]
      _ = ∫⁻ t, ‖ccm24LogRepresentative u t‖ₑ ^ (2 : ℕ)
          ∂volume := by
        apply lintegral_congr
        intro t
        exact ccm24LogToEvenHalfDensityRaw_exp_enorm_sq u t
  calc
    eLpNorm (ccm24LogToEvenHalfDensityRaw u) 2 volume =
        eLpNorm (ccm24LogRepresentative u) 2 volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num)]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num) (by norm_num)]
      norm_num
      exact congrArg (fun z : ENNReal => z ^ (1 / 2 : ℝ)) hrawIntegral
    _ = eLpNorm (u : ℝ → ℂ) 2 volume :=
      eLpNorm_congr_ae (ccm24LogRepresentative_ae_eq u).symm

theorem memLp_ccm24LogToEvenHalfDensityRaw
    (u : cc20GlobalLogCrossingL2) :
    MemLp (ccm24LogToEvenHalfDensityRaw u) 2 volume := by
  constructor
  · exact (measurable_ccm24LogToEvenHalfDensityRaw u).aestronglyMeasurable
  · rw [eLpNorm_ccm24LogToEvenHalfDensityRaw]
    exact (Lp.memLp u).2

noncomputable def ccm24LogToEvenHalfDensityLp
    (u : cc20GlobalLogCrossingL2) : cc20GlobalLogCrossingL2 :=
  (memLp_ccm24LogToEvenHalfDensityRaw u).toLp
    (ccm24LogToEvenHalfDensityRaw u)

theorem ccm24LogToEvenHalfDensityLp_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (ccm24LogToEvenHalfDensityLp u : ℝ → ℂ) =ᵐ[volume]
      ccm24LogToEvenHalfDensityRaw u :=
  (memLp_ccm24LogToEvenHalfDensityRaw u).coeFn_toLp

theorem ccm24LogToEvenHalfDensityLp_mem_even
    (u : cc20GlobalLogCrossingL2) :
    ccm24LogToEvenHalfDensityLp u ∈
      ccm24EvenAdditiveClosedSubspace := by
  rw [mem_ccm24EvenAdditiveClosedSubspace_iff_ae_even]
  have hcoe := ccm24LogToEvenHalfDensityLp_coeFn u
  have hcoeNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hcoe
  filter_upwards [hcoe, hcoeNeg] with x hx hxNeg
  simp only [Function.comp_apply] at hxNeg
  rw [hxNeg, hx, ccm24LogToEvenHalfDensityRaw_even]

/-- Explicit even preimage of a common-log vector. -/
noncomputable def ccm24LogToEvenHalfDensity
    (u : cc20GlobalLogCrossingL2) : ccm24EvenAdditiveL2 :=
  ⟨ccm24LogToEvenHalfDensityLp u,
    ccm24LogToEvenHalfDensityLp_mem_even u⟩

theorem ccm24EvenRepresentative_sub_explicitInverse_ae_zero
    (u : cc20GlobalLogCrossingL2) :
    (fun x =>
      ccm24EvenAdditiveRepresentative (ccm24LogToEvenHalfDensity u) x -
        ccm24LogToEvenHalfDensityRaw u x) =ᵐ[volume] 0 := by
  have hrep := ccm24EvenAdditiveRepresentative_ae_eq
    (ccm24LogToEvenHalfDensity u)
  have hinv := ccm24LogToEvenHalfDensityLp_coeFn u
  filter_upwards [hrep, hinv] with x hrepAt hinvAt
  change
    (((ccm24LogToEvenHalfDensity u : ccm24EvenAdditiveL2) :
      cc20GlobalLogCrossingL2) : ℝ → ℂ) x =
        ccm24LogToEvenHalfDensityRaw u x at hinvAt
  rw [← hrepAt, hinvAt]
  simp

theorem ccm24ForwardRepresentative_eq_explicitInverse_ae
    (u : cc20GlobalLogCrossingL2) :
    ccm24NormalizedLogHalfDensityRaw (ccm24LogToEvenHalfDensity u)
        =ᵐ[volume]
      ccm24NormalizedLogHalfDensityFunction
        (ccm24LogToEvenHalfDensityRaw u) := by
  let defect : ℝ → ℂ := fun x =>
    ccm24EvenAdditiveRepresentative (ccm24LogToEvenHalfDensity u) x -
      ccm24LogToEvenHalfDensityRaw u x
  have hdefectStrong : StronglyMeasurable defect :=
    (stronglyMeasurable_ccm24EvenAdditiveRepresentative
      (ccm24LogToEvenHalfDensity u)).sub
        (measurable_ccm24LogToEvenHalfDensityRaw u).stronglyMeasurable
  have hdefectZero : defect =ᵐ[volume] 0 :=
    ccm24EvenRepresentative_sub_explicitInverse_ae_zero u
  have htransportZero :=
    ccm24NormalizedLogHalfDensityFunction_ae_zero
      defect hdefectStrong hdefectZero
  filter_upwards [htransportZero] with t ht
  apply sub_eq_zero.mp
  simpa only [ccm24NormalizedLogHalfDensityRaw,
    ccm24NormalizedLogHalfDensityFunction, defect, Pi.zero_apply,
    smul_sub] using ht

theorem ccm24NormalizedLogHalfDensity_explicitInverse
    (u : cc20GlobalLogCrossingL2) (t : ℝ) :
    ccm24NormalizedLogHalfDensityFunction
        (ccm24LogToEvenHalfDensityRaw u) t =
      ccm24LogRepresentative u t := by
  rw [ccm24NormalizedLogHalfDensityFunction,
    ccm24LogToEvenHalfDensityRaw_exp, smul_smul]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hcoef :
      (Real.sqrt 2 * Real.exp (t / 2)) *
          ((1 / Real.sqrt 2) * Real.exp (-t / 2)) = 1 := by
    field_simp [hsqrt_pos.ne']
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [hcoef, one_smul]

/-- The explicit inverse is a right inverse of the normalized half-density
linear isometry. -/
theorem ccm24EvenToLogHalfDensity_rightInverse
    (u : cc20GlobalLogCrossingL2) :
    ccm24EvenToLogHalfDensity (ccm24LogToEvenHalfDensity u) = u := by
  rw [Lp.ext_iff]
  have hforward := ccm24EvenToLogHalfDensity_coeFn
    (ccm24LogToEvenHalfDensity u)
  have hcompare := ccm24ForwardRepresentative_eq_explicitInverse_ae u
  have hpoint :
      ∀ᵐ t ∂volume,
        ccm24NormalizedLogHalfDensityFunction
            (ccm24LogToEvenHalfDensityRaw u) t =
          ccm24LogRepresentative u t :=
    Filter.Eventually.of_forall
      (ccm24NormalizedLogHalfDensity_explicitInverse u)
  have hrep := ccm24LogRepresentative_ae_eq u
  filter_upwards [hforward, hcompare, hpoint, hrep] with
    t hforwardAt hcompareAt hpointAt hrepAt
  rw [hforwardAt, hcompareAt, hpointAt]
  exact hrepAt.symm

theorem ccm24EvenToLogHalfDensity_surjective :
    Function.Surjective ccm24EvenToLogHalfDensityLinearIsometry := by
  intro u
  exact ⟨ccm24LogToEvenHalfDensity u,
    ccm24EvenToLogHalfDensity_rightInverse u⟩

/-- The explicit unitary carrier identification
`L2(R)^ev ≃ L2(R, dt)` underlying CCM24's `w_infinity` followed by the
logarithmic coordinate. -/
noncomputable def ccm24EvenLogCarrierEquiv :
    ccm24EvenAdditiveL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  LinearIsometryEquiv.ofSurjective
    ccm24EvenToLogHalfDensityLinearIsometry
    ccm24EvenToLogHalfDensity_surjective

theorem ccm24EvenLogCarrierEquiv_apply
    (u : ccm24EvenAdditiveL2) :
    ccm24EvenLogCarrierEquiv u = ccm24EvenToLogHalfDensity u :=
  rfl

theorem ccm24EvenLogCarrierEquiv_symm_apply
    (u : cc20GlobalLogCrossingL2) :
    ccm24EvenLogCarrierEquiv.symm u = ccm24LogToEvenHalfDensity u := by
  apply ccm24EvenLogCarrierEquiv.injective
  rw [ccm24EvenLogCarrierEquiv.apply_symm_apply]
  exact (ccm24EvenToLogHalfDensity_rightInverse u).symm

set_option maxHeartbeats 800000 in
-- The dependent `toLp` representatives in the Schwartz-density step need a wider local budget.
/-- On whole-line `L2`, inverse Fourier is reflection after Fourier.  The
identity is first checked on Schwartz functions and then extended by density. -/
theorem ccm24_fourierInv_eq_reflection_fourier
    (u : cc20GlobalLogCrossingL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm u =
      ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u) := by
  let p : cc20GlobalLogCrossingL2 → Prop := fun u =>
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm u =
      ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) u
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
    · exact ccm24LogSpectralReflection.continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro f
    change
      𝓕⁻ (f.toLp 2) = ccm24LogSpectralReflection (𝓕 (f.toLp 2))
    rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
    let fi : SchwartzMap ℝ ℂ := 𝓕⁻ f
    let ff : SchwartzMap ℝ ℂ := 𝓕 f
    change fi.toLp 2 = ccm24LogSpectralReflection (ff.toLp 2)
    rw [Lp.ext_iff]
    have htoLp (g : SchwartzMap ℝ ℂ) :
        ((g.toLp 2 : cc20GlobalLogCrossingL2) : ℝ → ℂ)
          =ᵐ[volume] (g : ℝ → ℂ) :=
      (SchwartzMap.memLp g 2).coeFn_toLp
    have hinv :
        ((fi.toLp 2 : cc20GlobalLogCrossingL2) : ℝ → ℂ)
          =ᵐ[volume] (fi : ℝ → ℂ) :=
      htoLp fi
    have hfour := htoLp ff
    have hfourNeg :=
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq hfour
    have href := ccm24LogSpectralReflectionEquiv_coeFn (ff.toLp 2)
    filter_upwards [hinv, hfourNeg, href] with x hinvAt hfourNegAt hrefAt
    rw [hinvAt, hrefAt]
    have hpoint : fi x = ff (-x) := by
      simpa [fi, ff] using congrArg (fun g : SchwartzMap ℝ ℂ => g x)
        (SchwartzMap.fourierInv_apply_eq f)
    simpa only [Function.comp_apply] using hpoint.trans hfourNegAt.symm

/-- Equivalently, Fourier after reflection is inverse Fourier. -/
theorem ccm24_fourier_reflection_eq_fourierInv
    (u : cc20GlobalLogCrossingL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24LogSpectralReflection u) =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm u := by
  calc
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24LogSpectralReflection u) =
        Lp.fourierTransformₗᵢ ℝ ℂ
          ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
            ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u)) := by
      congr 1
      calc
        ccm24LogSpectralReflection u =
            ccm24LogSpectralReflection
              (Lp.fourierTransformₗᵢ ℝ ℂ
                ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u)) :=
          congrArg ccm24LogSpectralReflection
            ((Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply u).symm
        _ = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
            ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u) :=
          (ccm24_fourierInv_eq_reflection_fourier
            ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u)).symm
    _ = (Lp.fourierTransformₗᵢ ℝ ℂ).symm u := by simp

theorem ccm24_fourier_mem_even
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24EvenAdditiveClosedSubspace) :
    Lp.fourierTransformₗᵢ ℝ ℂ u ∈
      ccm24EvenAdditiveClosedSubspace := by
  rw [mem_ccm24EvenAdditiveClosedSubspace_iff] at hu ⊢
  calc
    ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u) =
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm u :=
      (ccm24_fourierInv_eq_reflection_fourier u).symm
    _ = Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24LogSpectralReflection u) :=
      (ccm24_fourier_reflection_eq_fourierInv u).symm
    _ = Lp.fourierTransformₗᵢ ℝ ℂ u := by rw [hu]

noncomputable def ccm24EvenAdditiveFourierLinearIsometry :
    ccm24EvenAdditiveL2 →ₗᵢ[ℂ] ccm24EvenAdditiveL2 where
  toFun u := ⟨Lp.fourierTransformₗᵢ ℝ ℂ u,
    ccm24_fourier_mem_even u.property⟩
  map_add' u v := by
    apply Subtype.ext
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_smul c u
  norm_map' u := by
    change ‖Lp.fourierTransformₗᵢ ℝ ℂ
      (u : cc20GlobalLogCrossingL2)‖ = ‖(u : cc20GlobalLogCrossingL2)‖
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map u

theorem ccm24EvenAdditiveFourierLinearIsometry_involutive :
    Function.Involutive ccm24EvenAdditiveFourierLinearIsometry := by
  intro u
  apply Subtype.ext
  change Lp.fourierTransformₗᵢ ℝ ℂ
      (Lp.fourierTransformₗᵢ ℝ ℂ (u : cc20GlobalLogCrossingL2)) = u
  have heven :=
    (mem_ccm24EvenAdditiveClosedSubspace_iff
      (u : cc20GlobalLogCrossingL2)).1 u.property
  have hsame :
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm u =
        Lp.fourierTransformₗᵢ ℝ ℂ u := by
    calc
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm u =
          Lp.fourierTransformₗᵢ ℝ ℂ
            (ccm24LogSpectralReflection u) :=
        (ccm24_fourier_reflection_eq_fourierInv u).symm
      _ = Lp.fourierTransformₗᵢ ℝ ℂ u := by rw [heven]
  rw [← hsame]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply u

/-- The genuine even additive Fourier involution on `L2(R)^ev`. -/
noncomputable def ccm24EvenAdditiveFourier :
    ccm24EvenAdditiveL2 ≃ₗᵢ[ℂ] ccm24EvenAdditiveL2 where
  toLinearEquiv := LinearEquiv.ofInvolutive
    ccm24EvenAdditiveFourierLinearIsometry.toLinearMap
    ccm24EvenAdditiveFourierLinearIsometry_involutive
  norm_map' := ccm24EvenAdditiveFourierLinearIsometry.norm_map

/-- Reflection on the bundled Schwartz space. -/
noncomputable def ccm24SchwartzReflectionCLM :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ))

theorem ccm24SchwartzReflectionCLM_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccm24SchwartzReflectionCLM f x = f (-x) :=
  rfl

/-- Bundled evenization of a Schwartz function. -/
noncomputable def ccm24EvenSchwartzSymmetrizationCLM :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ) +
      ccm24SchwartzReflectionCLM)

theorem ccm24EvenSchwartzSymmetrizationCLM_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccm24EvenSchwartzSymmetrizationCLM f x =
      (2 : ℂ)⁻¹ * (f x + f (-x)) :=
  rfl

theorem ccm24EvenSchwartzSymmetrizationCLM_even
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccm24EvenSchwartzSymmetrizationCLM f (-x) =
      ccm24EvenSchwartzSymmetrizationCLM f x := by
  rw [ccm24EvenSchwartzSymmetrizationCLM_apply,
    ccm24EvenSchwartzSymmetrizationCLM_apply]
  simp only [neg_neg]
  rw [add_comm]

/-- Average an `L2(R)` vector with its reflection.  Its range is exactly the
even closed subspace. -/
noncomputable def ccm24EvenSymmetrizationCLM :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 +
      ccm24LogSpectralReflection.toContinuousLinearEquiv.toContinuousLinearMap)

theorem ccm24EvenSymmetrizationCLM_apply
    (u : cc20GlobalLogCrossingL2) :
    ccm24EvenSymmetrizationCLM u =
      (2 : ℂ)⁻¹ • (u + ccm24LogSpectralReflection u) :=
  rfl

set_option maxHeartbeats 1200000 in
-- Comparing the two dependent `toLp` representatives needs one wider local budget.
/-- Bundled Schwartz evenization agrees exactly with the ambient `L2`
symmetrization. -/
theorem ccm24EvenSchwartzSymmetrization_toLp
    (f : SchwartzMap ℝ ℂ) :
    (ccm24EvenSchwartzSymmetrizationCLM f).toLp 2 =
      ccm24EvenSymmetrizationCLM (f.toLp 2) := by
  rw [ccm24EvenSymmetrizationCLM_apply, Lp.ext_iff]
  have htoLp (g : SchwartzMap ℝ ℂ) :
      ((g.toLp 2 : cc20GlobalLogCrossingL2) : ℝ → ℂ) =ᵐ[volume]
        (g : ℝ → ℂ) :=
    (SchwartzMap.memLp g 2).coeFn_toLp
  have heven := htoLp (ccm24EvenSchwartzSymmetrizationCLM f)
  have hf := htoLp f
  have hfNeg :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq hf
  have hsmul := Lp.coeFn_smul (2 : ℂ)⁻¹
    ((f.toLp 2 : cc20GlobalLogCrossingL2) +
      ccm24LogSpectralReflection (f.toLp 2))
  have hadd := Lp.coeFn_add (f.toLp 2 : cc20GlobalLogCrossingL2)
    (ccm24LogSpectralReflection (f.toLp 2))
  have hreflect := ccm24LogSpectralReflectionEquiv_coeFn (f.toLp 2)
  filter_upwards [heven, hf, hfNeg, hsmul, hadd, hreflect] with
      x hevenAt hfAt hfNegAt hsmulAt haddAt hreflectAt
  simp only [Function.comp_apply] at hfNegAt
  rw [hevenAt, hsmulAt]
  simp only [Pi.smul_apply]
  rw [haddAt]
  simp only [Pi.add_apply]
  rw [hreflectAt, hfAt, hfNegAt]
  simp only [ccm24EvenSchwartzSymmetrizationCLM_apply, smul_eq_mul]

theorem ccm24EvenSymmetrizationCLM_mem
    (u : cc20GlobalLogCrossingL2) :
    ccm24EvenSymmetrizationCLM u ∈
      ccm24EvenAdditiveClosedSubspace := by
  rw [mem_ccm24EvenAdditiveClosedSubspace_iff,
    ccm24EvenSymmetrizationCLM_apply]
  have hreflection :
      ccm24LogSpectralReflection
          (ccm24LogSpectralReflection u) = u :=
    ccm24LogSpectralReflection_involutive u
  simp only [map_smul, map_add, hreflection]
  rw [add_comm]

/-- Continuous symmetrization with codomain restricted to `L2(R)^ev`. -/
noncomputable def ccm24EvenSymmetrizationToEven :
    cc20GlobalLogCrossingL2 →L[ℂ] ccm24EvenAdditiveL2 :=
  ccm24EvenSymmetrizationCLM.codRestrict
    ccm24EvenAdditiveClosedSubspace.toSubmodule
    ccm24EvenSymmetrizationCLM_mem

/-- The same even vector, now retaining its genuine bundled Schwartz
representative. -/
noncomputable def ccm24BundledEvenSchwartzToEven
    (f : SchwartzMap ℝ ℂ) : ccm24EvenAdditiveL2 :=
  ccm24EvenSymmetrizationToEven (f.toLp 2)

theorem ccm24BundledEvenSchwartzToEven_coe
    (f : SchwartzMap ℝ ℂ) :
    (ccm24BundledEvenSchwartzToEven f : cc20GlobalLogCrossingL2) =
      (ccm24EvenSchwartzSymmetrizationCLM f).toLp 2 := by
  change ccm24EvenSymmetrizationCLM (f.toLp 2) = _
  exact (ccm24EvenSchwartzSymmetrization_toLp f).symm

/-- For the bundled even Schwartz vector, the common-log `L2`
representative is the explicit pointwise half-density of that same Schwartz
function. -/
theorem ccm24EvenToLogHalfDensity_bundledSchwartz_coeFn
    (f : SchwartzMap ℝ ℂ) :
    (ccm24EvenToLogHalfDensity
        (ccm24BundledEvenSchwartzToEven f) : ℝ → ℂ) =ᵐ[volume]
      ccm24NormalizedLogHalfDensityFunction
        (ccm24EvenSchwartzSymmetrizationCLM f) := by
  have hLp :=
    (SchwartzMap.memLp (ccm24EvenSchwartzSymmetrizationCLM f) 2).coeFn_toLp
  have hrep := ccm24EvenAdditiveRepresentative_ae_eq
    (ccm24BundledEvenSchwartzToEven f)
  rw [ccm24BundledEvenSchwartzToEven_coe] at hrep
  have hrepSchwartz :
      ccm24EvenAdditiveRepresentative
          (ccm24BundledEvenSchwartzToEven f) =ᵐ[volume]
        (ccm24EvenSchwartzSymmetrizationCLM f : ℝ → ℂ) :=
    hrep.symm.trans hLp
  exact (ccm24EvenToLogHalfDensity_coeFn
      (ccm24BundledEvenSchwartzToEven f)).trans
    (ccm24NormalizedLogHalfDensityFunction_congr_ae
      (stronglyMeasurable_ccm24EvenAdditiveRepresentative
        (ccm24BundledEvenSchwartzToEven f))
      (ccm24EvenSchwartzSymmetrizationCLM f).continuous.stronglyMeasurable
      hrepSchwartz)

theorem ccm24EvenSymmetrizationToEven_surjective :
    Function.Surjective ccm24EvenSymmetrizationToEven := by
  intro u
  refine ⟨(u : cc20GlobalLogCrossingL2), ?_⟩
  apply Subtype.ext
  change ccm24EvenSymmetrizationCLM
      (u : cc20GlobalLogCrossingL2) = u
  rw [ccm24EvenSymmetrizationCLM_apply]
  have hu :=
    (mem_ccm24EvenAdditiveClosedSubspace_iff
      (u : cc20GlobalLogCrossingL2)).1 u.property
  rw [hu, ← two_smul ℂ (u : cc20GlobalLogCrossingL2), ← mul_smul]
  norm_num

/-- Even Schwartz vectors, symmetrized in `L2` and transported through the
half-density isometry to the common logarithmic carrier. -/
noncomputable def ccm24EvenSchwartzToLog
    (f : SchwartzMap ℝ ℂ) : cc20GlobalLogCrossingL2 :=
  ccm24EvenLogCarrierEquiv
    (ccm24EvenSymmetrizationToEven (f.toLp 2))

theorem ccm24EvenSchwartzToLog_eq_bundled
    (f : SchwartzMap ℝ ℂ) :
    ccm24EvenSchwartzToLog f =
      ccm24EvenLogCarrierEquiv (ccm24BundledEvenSchwartzToEven f) := by
  rfl

theorem ccm24EvenSchwartzToLog_denseRange :
    DenseRange ccm24EvenSchwartzToLog := by
  have hSchwartz :
      DenseRange (fun f : SchwartzMap ℝ ℂ =>
        (f.toLp 2 : cc20GlobalLogCrossingL2)) :=
    SchwartzMap.denseRange_toLpCLM
      (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
  have hEven : DenseRange ccm24EvenSymmetrizationToEven :=
    ccm24EvenSymmetrizationToEven_surjective.denseRange
  have hLog : DenseRange ccm24EvenLogCarrierEquiv :=
    ccm24EvenLogCarrierEquiv.surjective.denseRange
  have hEvenSchwartz := hEven.comp hSchwartz
    ccm24EvenSymmetrizationToEven.continuous
  simpa only [ccm24EvenSchwartzToLog, Function.comp_apply] using
    hLog.comp hEvenSchwartz ccm24EvenLogCarrierEquiv.continuous

/-- The genuine source Fourier involution on the common logarithmic carrier,
obtained by transporting Mathlib's additive Fourier transform through the
independently constructed half-density isometry.  This is not defined through
`ccm24ArchimedeanHardyTitchmarsh`; their equality is the remaining
Fourier--Mellin functional equation. -/
noncomputable def ccm24ArchimedeanSourceFourier :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  ccm24EvenLogCarrierEquiv.symm.trans
    (ccm24EvenAdditiveFourier.trans ccm24EvenLogCarrierEquiv)

theorem ccm24ArchimedeanSourceFourier_apply
    (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanSourceFourier u =
      ccm24EvenLogCarrierEquiv
        (ccm24EvenAdditiveFourier (ccm24EvenLogCarrierEquiv.symm u)) :=
  rfl

/-- The genuine additive Fourier transform of the bundled even Schwartz
representative, retained inside the even `L2` carrier. -/
noncomputable def ccm24BundledEvenSchwartzFourierToEven
    (f : SchwartzMap ℝ ℂ) : ccm24EvenAdditiveL2 :=
  ⟨(𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)).toLp 2, by
    have hmem := ccm24_fourier_mem_even
      (ccm24BundledEvenSchwartzToEven f).property
    rw [ccm24BundledEvenSchwartzToEven_coe] at hmem
    have hFourier :
        Lp.fourierTransformₗᵢ ℝ ℂ
            ((ccm24EvenSchwartzSymmetrizationCLM f).toLp 2) =
          (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq
        (ccm24EvenSchwartzSymmetrizationCLM f)
    rw [hFourier] at hmem
    exact hmem⟩

/-- On the concrete dense family, the transported source Fourier transform
is exactly Mathlib's pointwise Schwartz Fourier transform before passage to
`L2`. -/
theorem ccm24ArchimedeanSourceFourier_evenSchwartz_readback
    (f : SchwartzMap ℝ ℂ) :
    ccm24ArchimedeanSourceFourier (ccm24EvenSchwartzToLog f) =
      ccm24EvenLogCarrierEquiv
        (ccm24BundledEvenSchwartzFourierToEven f) := by
  rw [ccm24EvenSchwartzToLog_eq_bundled]
  rw [ccm24ArchimedeanSourceFourier_apply,
    ccm24EvenLogCarrierEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  change
    Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24BundledEvenSchwartzToEven f : cc20GlobalLogCrossingL2) =
      (𝓕 (ccm24EvenSchwartzSymmetrizationCLM f)).toLp 2
  rw [ccm24BundledEvenSchwartzToEven_coe]
  exact SchwartzMap.toLp_fourier_eq
    (ccm24EvenSchwartzSymmetrizationCLM f)

theorem ccm24ArchimedeanSourceFourier_involutive :
    Function.Involutive ccm24ArchimedeanSourceFourier := by
  intro u
  rw [ccm24ArchimedeanSourceFourier_apply,
    ccm24ArchimedeanSourceFourier_apply,
    ccm24EvenLogCarrierEquiv.symm_apply_apply]
  have hfourier :
      ccm24EvenAdditiveFourier
          (ccm24EvenAdditiveFourier (ccm24EvenLogCarrierEquiv.symm u)) =
        ccm24EvenLogCarrierEquiv.symm u :=
    ccm24EvenAdditiveFourierLinearIsometry_involutive
      (ccm24EvenLogCarrierEquiv.symm u)
  rw [hfourier, ccm24EvenLogCarrierEquiv.apply_symm_apply]

/-- To identify the genuine source Fourier transform with the independently
constructed Hardy--Titchmarsh operator, it is enough to prove their equality
on the concrete dense family of even Schwartz vectors. -/
theorem ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh_of_evenSchwartz
    (hSchwartz : ∀ f : SchwartzMap ℝ ℂ,
      ccm24ArchimedeanSourceFourier (ccm24EvenSchwartzToLog f) =
        ccm24ArchimedeanHardyTitchmarsh (ccm24EvenSchwartzToLog f)) :
    ccm24ArchimedeanSourceFourier =
      ccm24ArchimedeanHardyTitchmarsh := by
  apply DFunLike.ext _ _
  intro u
  apply DenseRange.induction_on (p := fun v : cc20GlobalLogCrossingL2 =>
      ccm24ArchimedeanSourceFourier v =
        ccm24ArchimedeanHardyTitchmarsh v)
    ccm24EvenSchwartzToLog_denseRange u
  · exact isClosed_eq ccm24ArchimedeanSourceFourier.continuous
      ccm24ArchimedeanHardyTitchmarsh.continuous
  · exact hSchwartz

/-- The critical Mellin parameter corresponding to Mathlib's normalized
log-Fourier frequency `xi`. -/
noncomputable def ccm24CriticalMellinParameter (xi : ℝ) : ℂ :=
  (1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ)

theorem ccm24CriticalMellinParameter_one_sub (xi : ℝ) :
    1 - ccm24CriticalMellinParameter xi =
      (1 / 2 : ℂ) + Complex.I * (2 * Real.pi * xi : ℝ) := by
  rw [ccm24CriticalMellinParameter]
  ring

theorem ccm24CriticalMellinParameter_neg (xi : ℝ) :
    ccm24CriticalMellinParameter (-xi) =
      1 - ccm24CriticalMellinParameter xi := by
  rw [ccm24CriticalMellinParameter,
    ccm24CriticalMellinParameter_one_sub]
  push_cast
  ring

@[simp] theorem ccm24CriticalMellinParameter_re (xi : ℝ) :
    (ccm24CriticalMellinParameter xi).re = 1 / 2 := by
  simp [ccm24CriticalMellinParameter, Complex.mul_re]

@[simp] theorem ccm24CriticalMellinParameter_im (xi : ℝ) :
    (ccm24CriticalMellinParameter xi).im = -(2 * Real.pi * xi) := by
  simp [ccm24CriticalMellinParameter, Complex.mul_im]

theorem ccm24CriticalMellinParameter_im_div_two_pi (xi : ℝ) :
    (ccm24CriticalMellinParameter xi).im / (2 * Real.pi) = -xi := by
  rw [ccm24CriticalMellinParameter_im]
  field_simp [Real.pi_ne_zero]

theorem ccm24CriticalMellinParameter_one_sub_im_div_two_pi (xi : ℝ) :
    (1 - ccm24CriticalMellinParameter xi).im / (2 * Real.pi) = xi := by
  rw [← ccm24CriticalMellinParameter_neg]
  rw [ccm24CriticalMellinParameter_im_div_two_pi, neg_neg]

/-- Every Schwartz function has an absolutely convergent Mellin transform on
the CCM24 critical line.  The proof uses only continuity at the origin and
Schwartz decay at positive infinity. -/
theorem ccm24Schwartz_mellinConvergent_critical
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) :
    MellinConvergent (fun x : ℝ => f x)
      (ccm24CriticalMellinParameter xi) := by
  apply mellinConvergent_of_isBigO_rpow
      (f.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
      (a := 1) (b := 0)
  · have hdecay :=
      (f.isBigO_cocompact_rpow (-1)).mono
        (_root_.atTop_le_cocompact : atTop ≤ cocompact ℝ)
    refine hdecay.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx]
  · rw [ccm24CriticalMellinParameter_re]
    norm_num
  · have hbounded :
        (fun x : ℝ => f x) =O[𝓝 (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto f.continuous.continuousAt one_ne_zero
    simpa using hbounded.mono
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  · rw [ccm24CriticalMellinParameter_re]
    norm_num

/-- The reflected critical Mellin integral of a Schwartz function converges
absolutely as well. -/
theorem ccm24Schwartz_mellinConvergent_one_sub_critical
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) :
    MellinConvergent (fun x : ℝ => f x)
      (1 - ccm24CriticalMellinParameter xi) := by
  rw [← ccm24CriticalMellinParameter_neg]
  exact ccm24Schwartz_mellinConvergent_critical f (-xi)

/-- The same critical convergence statements apply to the genuine Schwartz
Fourier transform. -/
theorem ccm24SchwartzFourier_mellinConvergent_critical
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) :
    MellinConvergent (fun x : ℝ => (𝓕 f) x)
      (ccm24CriticalMellinParameter xi) :=
  ccm24Schwartz_mellinConvergent_critical (𝓕 f) xi

theorem ccm24SchwartzFourier_mellinConvergent_one_sub_critical
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) :
    MellinConvergent (fun x : ℝ => (𝓕 f) x)
      (1 - ccm24CriticalMellinParameter xi) :=
  ccm24Schwartz_mellinConvergent_one_sub_critical (𝓕 f) xi

/-- The logarithmic profile appearing in Mathlib's Mellin-to-Fourier change
of variables at real part `1/2`. -/
noncomputable def ccm24CriticalMellinLogProfile
    (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Real.exp (-t / 2) • f (Real.exp (-t))

private theorem ccm24_rexpNeg_deriv :
    ∀ x ∈ Set.univ,
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem ccm24_rexpNeg_image :
    (Real.exp ∘ Neg.neg) '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

private theorem ccm24_rexpNeg_injOn :
    Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

private theorem ccm24_rexp_cpow_weight
    (x : ℝ) (s : ℂ) (z : ℂ) :
    Complex.exp (-x) * (Complex.exp (-x) ^ (s - 1) * z) =
      Complex.exp (-s * x) * z := by
  nth_rewrite 1 [← Complex.cpow_one (Complex.exp (-x))]
  rw [← mul_assoc]
  rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _),
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

/-- Absolute Mellin convergence is exactly absolute integrability of the
logarithmic Mellin profile.  This public bridge is the change of variables
`x = exp (-t)` used internally by Mellin inversion, exposed here because the
CCM24 carrier comparison needs the actual `L1` representative. -/
theorem integrable_mellinLogProfile_of_mellinConvergent
    (f : ℝ → ℂ) (sigma : ℝ)
    (hf : MellinConvergent f (sigma : ℂ)) :
    Integrable
      (fun t : ℝ => Real.exp (-sigma * t) • f (Real.exp (-t))) volume := by
  rw [MellinConvergent, ← ccm24_rexpNeg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ ccm24_rexpNeg_deriv ccm24_rexpNeg_injOn] at hf
  have hcomplex : Integrable
      (fun t : ℝ => Complex.exp (-(sigma : ℂ) * t) •
        f (Real.exp (-t))) volume := by
    simpa [ccm24_rexp_cpow_weight] using hf
  norm_cast at hcomplex

/-- Chain-rule term for an unbundled differentiable source function. -/
noncomputable def ccm24CriticalMellinLogProfileFunctionChainDeriv
    (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Real.exp (-t / 2) •
    ((-Real.exp (-t)) • deriv f (Real.exp (-t)))

theorem hasDerivAt_ccm24CriticalMellinLogProfile_of_differentiable
    (f : ℝ → ℂ) (hf : Differentiable ℝ f) (t : ℝ) :
    HasDerivAt (ccm24CriticalMellinLogProfile f)
      (ccm24CriticalMellinLogProfileFunctionChainDeriv f t +
        ((-1 / 2 : ℝ) * Real.exp (-t / 2)) • f (Real.exp (-t))) t := by
  have hweight : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      ((-1 / 2 : ℝ) * Real.exp (-t / 2)) t := by
    convert (Real.hasDerivAt_exp (-t / 2)).comp t
      ((hasDerivAt_neg t).div_const 2) using 1
    ring
  have hexpNeg : HasDerivAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) using 1
    ring
  have hfComp : HasDerivAt (fun u : ℝ => f (Real.exp (-u)))
      ((-Real.exp (-t)) • deriv f (Real.exp (-t))) t :=
    (hf (Real.exp (-t))).hasDerivAt.scomp t hexpNeg
  simpa only [ccm24CriticalMellinLogProfile,
    ccm24CriticalMellinLogProfileFunctionChainDeriv] using
      hweight.smul hfComp

theorem continuous_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    Continuous (ccm24CriticalMellinLogProfile f) := by
  unfold ccm24CriticalMellinLogProfile
  fun_prop

/-- A Schwartz function's critical Mellin profile is absolutely integrable
on the logarithmic line.  The positive log tail uses boundedness of `f`; the
negative log tail uses one full power of Schwartz decay. -/
theorem integrable_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    Integrable (ccm24CriticalMellinLogProfile f) volume := by
  have hmeas : AEStronglyMeasurable
      (ccm24CriticalMellinLogProfile f) volume :=
    (continuous_ccm24CriticalMellinLogProfile f).aestronglyMeasurable
  let C0 : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  let C1 : ℝ := SchwartzMap.seminorm ℂ 1 0 f
  have hposMajorant : IntegrableOn
      (fun t : ℝ => C0 * Real.exp ((-1 / 2 : ℝ) * t))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) 0).const_mul C0
  have hpos : IntegrableOn (ccm24CriticalMellinLogProfile f)
      (Set.Ioi 0) volume := by
    apply hposMajorant.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ccm24CriticalMellinLogProfile, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * ‖f (Real.exp (-t))‖ ≤
          Real.exp (-t / 2) * C0 := by
        gcongr
        exact SchwartzMap.norm_le_seminorm ℂ f (Real.exp (-t))
      _ = C0 * Real.exp ((-1 / 2 : ℝ) * t) := by
        ring_nf
  have hnegMajorant : IntegrableOn
      (fun t : ℝ => C1 * Real.exp ((1 / 2 : ℝ) * t))
      (Set.Iic 0) volume :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul C1
  have hneg : IntegrableOn (ccm24CriticalMellinLogProfile f)
      (Set.Iic 0) volume := by
    apply hnegMajorant.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 1
      (Real.exp (-t))
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one] at hdecay
    rw [ccm24CriticalMellinLogProfile, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * ‖f (Real.exp (-t))‖ =
          Real.exp (t / 2) *
            (Real.exp (-t) * ‖f (Real.exp (-t))‖) := by
        have hexp : Real.exp (-t / 2) =
            Real.exp (t / 2) * Real.exp (-t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
      _ ≤ Real.exp (t / 2) * C1 :=
        mul_le_mul_of_nonneg_left hdecay (Real.exp_nonneg _)
      _ = C1 * Real.exp ((1 / 2 : ℝ) * t) := by
        ring_nf
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

/-- The critical profile is simultaneously an `L1` and an `L2` function;
this is the exact common domain needed by the classical Fourier integral and
the Plancherel Fourier operator. -/
theorem memLp_one_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    MemLp (ccm24CriticalMellinLogProfile f) 1 volume :=
  memLp_one_iff_integrable.mpr
    (integrable_ccm24CriticalMellinLogProfile f)

/-- The critical Mellin profile as an actual `L1` vector. -/
noncomputable def ccm24CriticalMellinLogProfileL1
    (f : SchwartzMap ℝ ℂ) : Lp ℂ 1 (volume : Measure ℝ) :=
  (memLp_one_ccm24CriticalMellinLogProfile f).toLp
    (ccm24CriticalMellinLogProfile f)

theorem ccm24CriticalMellinLogProfileL1_coeFn
    (f : SchwartzMap ℝ ℂ) :
    (ccm24CriticalMellinLogProfileL1 f : ℝ → ℂ) =ᵐ[volume]
      ccm24CriticalMellinLogProfile f :=
  (memLp_one_ccm24CriticalMellinLogProfile f).coeFn_toLp

/- Compatibility of the classical Fourier integral with the Plancherel
`L2` Fourier transform on their genuine common domain.  The proof tests both
vectors against the dense Schwartz image and uses the Fourier Fubini identity;
it does not identify the two transforms by definition. -/
set_option maxHeartbeats 800000 in
-- The dense-test-vector proof elaborates several nested Fourier/Lp coercions.
theorem ccm24_fourierTransformL2_eq_classical_toLp
    (g : ℝ → ℂ)
    (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume)
    (hfourier2 : MemLp (𝓕 g) 2 volume) :
    Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g) =
      hfourier2.toLp (𝓕 g) := by
  apply SchwartzMap.denseRange_toLpCLM
    (F := ℂ) (p := 2) ENNReal.ofNat_ne_top |>.eq_of_inner_left ℂ
  intro phi
  have hphiInv :
      (((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) : ℝ → ℂ) =ᵐ[volume]
        ((𝓕⁻ phi : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    have hvec :
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2) =
          (𝓕⁻ phi : SchwartzMap ℝ ℂ).toLp 2 := by
      change 𝓕⁻ (phi.toLp 2) = (𝓕⁻ phi : SchwartzMap ℝ ℂ).toLp 2
      exact SchwartzMap.toLp_fourierInv_eq phi
    rw [hvec]
    exact (𝓕⁻ phi : SchwartzMap ℝ ℂ).coeFn_toLp 2 volume
  have hswap :
      (∫ xi : ℝ, inner ℂ (𝓕 g xi) (phi xi) ∂volume) =
        ∫ x : ℝ, inner ℂ (g x) ((𝓕⁻ phi : SchwartzMap ℝ ℂ) x) ∂volume := by
    simpa [SchwartzMap.fourierInv_coe] using
      (VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
        (μ := volume) (ν := volume) (L := innerₗ ℝ)
        (innerSL ℂ) Real.continuous_fourierChar continuous_inner hg1 phi.integrable)
  calc
    inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g)) (phi.toLp 2) =
        inner ℂ (hg2.toLp g)
          ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) := by
      calc
        inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g)) (phi.toLp 2) =
            inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g))
              (Lp.fourierTransformₗᵢ ℝ ℂ
                ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2))) := by
          rw [(Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply]
        _ = inner ℂ (hg2.toLp g)
              ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) :=
          (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map _ _
    _ = ∫ x : ℝ, inner ℂ (g x)
        ((𝓕⁻ phi : SchwartzMap ℝ ℂ) x) ∂volume := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp, hphiInv] with x hgAt hphiAt
      rw [hgAt, hphiAt]
    _ = ∫ xi : ℝ, inner ℂ (𝓕 g xi) (phi xi) ∂volume := hswap.symm
    _ = inner ℂ (hfourier2.toLp (𝓕 g)) (phi.toLp 2) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfourier2.coeFn_toLp, phi.coeFn_toLp 2 volume] with
        xi hfourierAt hphiAt
      rw [hfourierAt, hphiAt]

/-- A one-dimensional first-order Sobolev criterion tailored to the bridge
above: if `g` and its derivative are integrable, then the classical Fourier
transform of `g` is square-integrable.  The proof keeps both estimates

`‖F g(x)‖ <= ‖g‖₁` and `|x| ‖F g(x)‖ <= ‖g'‖₁`

and combines them into the integrable majorant
`C * (1 + |x|)⁻¹`. -/
theorem memLp_two_fourier_of_integrable_deriv
    (g : ℝ → ℂ)
    (hg : Integrable g volume)
    (hgDiff : Differentiable ℝ g)
    (hgDeriv : Integrable (deriv g) volume) :
    MemLp (𝓕 g) 2 volume := by
  have hfourierContinuous : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hg
  let C0 : ℝ := ∫ x : ℝ, ‖g x‖ ∂volume
  let C1 : ℝ := ∫ x : ℝ, ‖deriv g x‖ ∂volume
  let C : ℝ := C0 + C1
  let majorant : ℝ → ℝ := fun x => C * (1 + ‖x‖) ^ (-1 : ℝ)
  have hC0 : 0 ≤ C0 := integral_nonneg fun _ => norm_nonneg _
  have hC1 : 0 ≤ C1 := integral_nonneg fun _ => norm_nonneg _
  have hmajorantMemLp : MemLp majorant 2 volume := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have hbase : Integrable
        (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
      integrable_one_add_norm (E := ℝ) (μ := volume) (r := (2 : ℝ)) (by norm_num)
    have hscaled := hbase.const_mul (C ^ 2)
    convert hscaled using 1
    funext x
    simp only [majorant, mul_pow]
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_one, Real.rpow_two]
    field_simp [show 1 + ‖x‖ ≠ 0 by positivity]
  apply hmajorantMemLp.mono' hfourierContinuous.aestronglyMeasurable
  filter_upwards with x
  have hzero : ‖𝓕 g x‖ ≤ C0 :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) g x
  have hderivIdentity := congrFun (Real.fourier_deriv hg hgDiff hgDeriv) x
  have hweighted : ‖x‖ * ‖𝓕 g x‖ ≤ C1 := by
    calc
      ‖x‖ * ‖𝓕 g x‖ ≤
          (2 * Real.pi) * (‖x‖ * ‖𝓕 g x‖) := by
        apply le_mul_of_one_le_left (by positivity)
        nlinarith [Real.one_le_pi_div_two]
      _ = ‖((2 * Real.pi : ℂ) * Complex.I * (x : ℂ)) • 𝓕 g x‖ := by
        simp only [norm_smul, norm_mul, Complex.norm_real, Complex.norm_I,
          Real.norm_eq_abs, mul_one]
        norm_num [abs_of_nonneg Real.pi_nonneg]
        ring
      _ = ‖𝓕 (deriv g) x‖ := by rw [← hderivIdentity]
      _ ≤ C1 :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          𝐞 volume (innerₗ ℝ) (deriv g) x
  have hsum : (1 + ‖x‖) * ‖𝓕 g x‖ ≤ C := by
    dsimp only [C]
    calc
      (1 + ‖x‖) * ‖𝓕 g x‖ =
          ‖𝓕 g x‖ + ‖x‖ * ‖𝓕 g x‖ := by ring
      _ ≤ C0 + C1 := add_le_add hzero hweighted
  have hden : 0 < 1 + ‖x‖ := by positivity
  calc
    ‖𝓕 g x‖ ≤ C / (1 + ‖x‖) :=
      (le_div_iff₀ hden).2 (by simpa [mul_comm] using hsum)
    _ = majorant x := by
      simp only [majorant, Real.rpow_neg_one]
      rw [div_eq_mul_inv]

/-- The chain-rule term in the derivative of the critical Mellin profile. -/
noncomputable def ccm24CriticalMellinLogProfileChainDeriv
    (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  Real.exp (-t / 2) •
    ((-Real.exp (-t)) •
      (SchwartzMap.derivCLM ℝ ℂ f) (Real.exp (-t)))

theorem integrable_ccm24CriticalMellinLogProfileChainDeriv
    (f : SchwartzMap ℝ ℂ) :
    Integrable (ccm24CriticalMellinLogProfileChainDeriv f) volume := by
  let df : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ f
  have hmeas : AEStronglyMeasurable
      (ccm24CriticalMellinLogProfileChainDeriv f) volume := by
    apply Continuous.aestronglyMeasurable
    unfold ccm24CriticalMellinLogProfileChainDeriv
    fun_prop
  let C0 : ℝ := SchwartzMap.seminorm ℂ 0 0 df
  let C2 : ℝ := SchwartzMap.seminorm ℂ 2 0 df
  have hposMajorant : IntegrableOn
      (fun t : ℝ => C0 * Real.exp ((-3 / 2 : ℝ) * t))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := (-3 / 2 : ℝ)) (by norm_num) 0).const_mul C0
  have hpos : IntegrableOn (ccm24CriticalMellinLogProfileChainDeriv f)
      (Set.Ioi 0) volume := by
    apply hposMajorant.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change
      ‖Real.exp (-t / 2) •
        ((-Real.exp (-t)) • df (Real.exp (-t)))‖ ≤ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * (Real.exp (-t) * ‖df (Real.exp (-t))‖) =
          Real.exp ((-3 / 2 : ℝ) * t) * ‖df (Real.exp (-t))‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp ((-3 / 2 : ℝ) * t) * C0 := by
        gcongr
        exact SchwartzMap.norm_le_seminorm ℂ df (Real.exp (-t))
      _ = C0 * Real.exp ((-3 / 2 : ℝ) * t) := by ring
  have hnegMajorant : IntegrableOn
      (fun t : ℝ => C2 * Real.exp ((1 / 2 : ℝ) * t))
      (Set.Iic 0) volume :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul C2
  have hneg : IntegrableOn (ccm24CriticalMellinLogProfileChainDeriv f)
      (Set.Iic 0) volume := by
    apply hnegMajorant.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℂ df 2
      (Real.exp (-t))
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hdecay
    change
      ‖Real.exp (-t / 2) •
        ((-Real.exp (-t)) • df (Real.exp (-t)))‖ ≤ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t / 2) * (Real.exp (-t) * ‖df (Real.exp (-t))‖) =
          Real.exp (t / 2) *
            (Real.exp (-t) ^ 2 * ‖df (Real.exp (-t))‖) := by
        have hexp : Real.exp (-t / 2) * Real.exp (-t) =
            Real.exp (t / 2) * (Real.exp (-t) ^ 2) := by
          rw [pow_two]
          simp only [← Real.exp_add]
          congr 1
          ring
        calc
          Real.exp (-t / 2) * (Real.exp (-t) * ‖df (Real.exp (-t))‖) =
              (Real.exp (-t / 2) * Real.exp (-t)) *
                ‖df (Real.exp (-t))‖ := by ring
          _ = (Real.exp (t / 2) * Real.exp (-t) ^ 2) *
                ‖df (Real.exp (-t))‖ := by rw [hexp]
          _ = Real.exp (t / 2) *
                (Real.exp (-t) ^ 2 * ‖df (Real.exp (-t))‖) := by ring
      _ ≤ Real.exp (t / 2) * C2 :=
        mul_le_mul_of_nonneg_left hdecay (Real.exp_nonneg _)
      _ = C2 * Real.exp ((1 / 2 : ℝ) * t) := by ring_nf
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

theorem hasDerivAt_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (ccm24CriticalMellinLogProfile f)
      (ccm24CriticalMellinLogProfileChainDeriv f t +
        ((-1 / 2 : ℝ) * Real.exp (-t / 2)) • f (Real.exp (-t))) t := by
  have hweight : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      ((-1 / 2 : ℝ) * Real.exp (-t / 2)) t := by
    convert (Real.hasDerivAt_exp (-t / 2)).comp t
      ((hasDerivAt_neg t).div_const 2) using 1
    ring
  have hexpNeg : HasDerivAt (fun u : ℝ => Real.exp (-u))
      (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) using 1
    ring
  have hfComp : HasDerivAt (fun u : ℝ => f (Real.exp (-u)))
      ((-Real.exp (-t)) • (SchwartzMap.derivCLM ℝ ℂ f) (Real.exp (-t))) t := by
    have hfAt : HasDerivAt (fun x : ℝ => f x)
        (deriv (fun x : ℝ => f x) (Real.exp (-t))) (Real.exp (-t)) :=
      f.differentiableAt.hasDerivAt
    exact hfAt.scomp t hexpNeg
  simpa only [ccm24CriticalMellinLogProfile,
    ccm24CriticalMellinLogProfileChainDeriv] using hweight.smul hfComp

theorem differentiable_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (ccm24CriticalMellinLogProfile f) :=
  fun t => (hasDerivAt_ccm24CriticalMellinLogProfile f t).differentiableAt

theorem integrable_deriv_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    Integrable (deriv (ccm24CriticalMellinLogProfile f)) volume := by
  have hchain := integrable_ccm24CriticalMellinLogProfileChainDeriv f
  have hweight := (integrable_ccm24CriticalMellinLogProfile f).const_mul
    ((-1 / 2 : ℝ) : ℂ)
  have hsum : Integrable
      (fun t => ccm24CriticalMellinLogProfileChainDeriv f t +
        ((-1 / 2 : ℝ) : ℂ) * ccm24CriticalMellinLogProfile f t) volume :=
    hchain.add hweight
  apply hsum.congr
  filter_upwards with t
  rw [(hasDerivAt_ccm24CriticalMellinLogProfile f t).deriv]
  congr 1
  change
    ((-1 / 2 : ℝ) : ℂ) *
        ((Real.exp (-t / 2) : ℂ) * f (Real.exp (-t))) =
      (((-1 / 2 : ℝ) * Real.exp (-t / 2) : ℝ) : ℂ) *
        f (Real.exp (-t))
  push_cast
  ring

/-- The classical Fourier transform of every critical Schwartz Mellin profile
is an actual `L2` function. -/
theorem memLp_two_fourier_ccm24CriticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    MemLp (𝓕 (ccm24CriticalMellinLogProfile f)) 2 volume :=
  memLp_two_fourier_of_integrable_deriv
    (ccm24CriticalMellinLogProfile f)
    (integrable_ccm24CriticalMellinLogProfile f)
    (differentiable_ccm24CriticalMellinLogProfile f)
    (integrable_deriv_ccm24CriticalMellinLogProfile f)

theorem ccm24NormalizedLogHalfDensityFunction_neg_eq_profile
    (f : ℝ → ℂ) (t : ℝ) :
    ccm24NormalizedLogHalfDensityFunction f (-t) =
      (Real.sqrt 2 : ℂ) * ccm24CriticalMellinLogProfile f t := by
  change
    (Real.sqrt 2 * Real.exp ((-t) / 2) : ℝ) * f (Real.exp (-t)) =
      (Real.sqrt 2 : ℂ) *
        ((Real.exp (-t / 2) : ℝ) * f (Real.exp (-t)))
  push_cast
  ring

theorem ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity
    (f : ℝ → ℂ) (t : ℝ) :
    ccm24CriticalMellinLogProfile f t =
      (1 / Real.sqrt 2 : ℂ) •
        ccm24NormalizedLogHalfDensityFunction f (-t) := by
  rw [ccm24NormalizedLogHalfDensityFunction_neg_eq_profile]
  simp only [smul_eq_mul]
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [hsqrt]

theorem ccm24EvenSchwartzToLog_coeFn
    (f : SchwartzMap ℝ ℂ) :
    (ccm24EvenSchwartzToLog f : ℝ → ℂ) =ᵐ[volume]
      ccm24NormalizedLogHalfDensityFunction
        (ccm24EvenSchwartzSymmetrizationCLM f) := by
  rw [ccm24EvenSchwartzToLog_eq_bundled,
    ccm24EvenLogCarrierEquiv_apply]
  exact ccm24EvenToLogHalfDensity_bundledSchwartz_coeFn f

theorem memLp_ccm24EvenSchwartz_criticalMellinLogProfile
    (f : SchwartzMap ℝ ℂ) :
    MemLp
      (ccm24CriticalMellinLogProfile
        (ccm24EvenSchwartzSymmetrizationCLM f)) 2 volume := by
  have hhalfDensity : MemLp
      (ccm24NormalizedLogHalfDensityFunction
        (ccm24EvenSchwartzSymmetrizationCLM f)) 2 volume :=
    (memLp_congr_ae (ccm24EvenSchwartzToLog_coeFn f)).mp
      (Lp.memLp (ccm24EvenSchwartzToLog f))
  have hreflected := hhalfDensity.comp_measurePreserving
    (Measure.measurePreserving_neg volume)
  have hscaled := hreflected.const_smul (1 / Real.sqrt 2 : ℂ)
  apply (memLp_congr_ae ?_).mpr hscaled
  filter_upwards [] with t
  simpa only [Pi.smul_apply, Function.comp_apply] using
    ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity
      (ccm24EvenSchwartzSymmetrizationCLM f) t

/-- The critical Mellin log profile of a bundled even Schwartz vector as an
actual `L2` vector. -/
noncomputable def ccm24EvenSchwartzCriticalMellinProfileL2
    (f : SchwartzMap ℝ ℂ) : cc20GlobalLogCrossingL2 :=
  (memLp_ccm24EvenSchwartz_criticalMellinLogProfile f).toLp
    (ccm24CriticalMellinLogProfile
      (ccm24EvenSchwartzSymmetrizationCLM f))

theorem ccm24EvenSchwartzCriticalMellinProfileL2_coeFn
    (f : SchwartzMap ℝ ℂ) :
    (ccm24EvenSchwartzCriticalMellinProfileL2 f : ℝ → ℂ) =ᵐ[volume]
      ccm24CriticalMellinLogProfile
        (ccm24EvenSchwartzSymmetrizationCLM f) :=
  (memLp_ccm24EvenSchwartz_criticalMellinLogProfile f).coeFn_toLp

/-- The Mellin log profile is exactly reflected normalized half-density,
including the `sqrt 2` normalization. -/
theorem ccm24EvenSchwartzCriticalMellinProfileL2_eq_reflection
    (f : SchwartzMap ℝ ℂ) :
    ccm24EvenSchwartzCriticalMellinProfileL2 f =
      (1 / Real.sqrt 2 : ℂ) •
        ccm24LogSpectralReflection (ccm24EvenSchwartzToLog f) := by
  rw [Lp.ext_iff]
  have hlogNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (ccm24EvenSchwartzToLog_coeFn f)
  filter_upwards
    [ccm24EvenSchwartzCriticalMellinProfileL2_coeFn f,
     Lp.coeFn_smul (1 / Real.sqrt 2 : ℂ)
      (ccm24LogSpectralReflection (ccm24EvenSchwartzToLog f)),
     ccm24LogSpectralReflectionEquiv_coeFn
      (ccm24EvenSchwartzToLog f),
     hlogNeg] with t hprofile hsmul hreflect hlogNegAt
  simp only [Function.comp_apply] at hlogNegAt
  rw [hprofile, hsmul]
  simp only [Pi.smul_apply]
  rw [hreflect, hlogNegAt]
  exact ccm24CriticalMellinLogProfile_eq_invSqrt_smul_negHalfDensity
    (ccm24EvenSchwartzSymmetrizationCLM f) t

/-- Unconditional classical/Plancherel compatibility for the actual critical
Mellin profile of a bundled even Schwartz source vector. -/
theorem ccm24EvenSchwartzCriticalMellinProfile_fourierTransformL2_eq_classical
    (f : SchwartzMap ℝ ℂ) :
    Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24EvenSchwartzCriticalMellinProfileL2 f) =
      (memLp_two_fourier_ccm24CriticalMellinLogProfile
        (ccm24EvenSchwartzSymmetrizationCLM f)).toLp
          (𝓕 (ccm24CriticalMellinLogProfile
            (ccm24EvenSchwartzSymmetrizationCLM f))) := by
  exact ccm24_fourierTransformL2_eq_classical_toLp
    (ccm24CriticalMellinLogProfile
      (ccm24EvenSchwartzSymmetrizationCLM f))
    (integrable_ccm24CriticalMellinLogProfile
      (ccm24EvenSchwartzSymmetrizationCLM f))
    (memLp_ccm24EvenSchwartz_criticalMellinLogProfile f)
    (memLp_two_fourier_ccm24CriticalMellinLogProfile
      (ccm24EvenSchwartzSymmetrizationCLM f))

/-- Exact Mellin/log-Fourier coordinate identity at
`s = 1/2 - 2*pi*i*xi`. -/
theorem ccm24_mellin_eq_fourier_criticalLogProfile
    (f : ℝ → ℂ) (xi : ℝ) :
    mellin f (ccm24CriticalMellinParameter xi) =
      𝓕 (ccm24CriticalMellinLogProfile f) (-xi) := by
  rw [mellin_eq_fourier,
    ccm24CriticalMellinParameter_im_div_two_pi]
  apply congrArg (fun g : ℝ → ℂ => 𝓕 g (-xi))
  funext t
  simp only [ccm24CriticalMellinParameter_re,
    ccm24CriticalMellinLogProfile]
  congr 2
  ring

/-- The reflected critical Mellin value uses the positive log-Fourier
frequency on the same profile. -/
theorem ccm24_mellin_one_sub_eq_fourier_criticalLogProfile
    (f : ℝ → ℂ) (xi : ℝ) :
    mellin f (1 - ccm24CriticalMellinParameter xi) =
      𝓕 (ccm24CriticalMellinLogProfile f) xi := by
  rw [mellin_eq_fourier,
    ccm24CriticalMellinParameter_one_sub_im_div_two_pi]
  apply congrArg (fun g : ℝ → ℂ => 𝓕 g xi)
  funext t
  have hreal : (1 - ccm24CriticalMellinParameter xi).re = 1 / 2 := by
    rw [← ccm24CriticalMellinParameter_neg]
    exact ccm24CriticalMellinParameter_re (-xi)
  rw [hreal]
  simp only [ccm24CriticalMellinLogProfile]
  congr 2
  ring

/-- Pointwise critical-line Fourier--Mellin functional equation for a source
function and its genuine additive Fourier transform. -/
def CCM24CriticalFourierMellinFunctionalEquation
    (f fourierF : ℝ → ℂ) : Prop :=
  ∀ xi : ℝ,
    mellin fourierF (ccm24CriticalMellinParameter xi) =
      ccm24ArchimedeanScatteringPhase xi *
        mellin f (1 - ccm24CriticalMellinParameter xi)

/-- The critical Fourier--Mellin equation is exactly the spectral multiplier
identity for the two concrete logarithmic profiles. -/
theorem ccm24CriticalFourierMellinFunctionalEquation_iff_logFourier
    (f fourierF : ℝ → ℂ) :
    CCM24CriticalFourierMellinFunctionalEquation f fourierF ↔
      ∀ xi : ℝ,
        𝓕 (ccm24CriticalMellinLogProfile fourierF) (-xi) =
          ccm24ArchimedeanScatteringPhase xi *
            𝓕 (ccm24CriticalMellinLogProfile f) xi := by
  simp only [CCM24CriticalFourierMellinFunctionalEquation,
    ccm24_mellin_eq_fourier_criticalLogProfile,
    ccm24_mellin_one_sub_eq_fourier_criticalLogProfile]

/-- The archimedean scattering phase is exactly the Mellin transform of the
even Fourier kernel: `Gamma_C(s) * cos(pi*s/2)`.  This is the algebraic Gamma
factor in the Fourier--Mellin functional equation, with no stored premise. -/
theorem ccm24ArchimedeanScatteringPhase_eq_cosineMellinCoefficient
    (xi : ℝ) :
    ccm24ArchimedeanScatteringPhase xi =
      Complex.Gammaℂ (ccm24CriticalMellinParameter xi) *
        Complex.cos
          (Real.pi * ccm24CriticalMellinParameter xi / 2) := by
  have hs : ∀ n : ℕ,
      ccm24CriticalMellinParameter xi ≠ -(2 * n + 1) := by
    intro n h
    have hre := congrArg Complex.re h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num [ccm24CriticalMellinParameter, Complex.mul_re] at hre
    linarith
  rw [ccm24ArchimedeanScatteringPhase_eq_factor_ratio]
  change
    Complex.Gammaℝ (ccm24CriticalMellinParameter xi) /
        Complex.Gammaℝ (ccm24CriticalMellinParameter (-xi)) = _
  rw [ccm24CriticalMellinParameter_neg]
  exact Complex.Gammaℝ_div_Gammaℝ_one_sub hs

/-- The positive multiplicative real line. -/
abbrev CCM24PositiveReal := Set.Ioi (0 : ℝ)

/-- Multiplicative Haar measure `d rho / rho`, defined in its canonical
logarithmic coordinate as the pushforward of Lebesgue measure by `exp`. -/
noncomputable def ccm24MultiplicativeHaarMeasure :
    Measure CCM24PositiveReal :=
  Measure.map Real.expOrderIso volume

/-- The genuine multiplicative Haar `L2` carrier used between `w_infinity`
and the multiplicative Fourier transform. -/
noncomputable abbrev ccm24MultiplicativeHaarL2 :=
  Lp ℂ 2 ccm24MultiplicativeHaarMeasure

theorem ccm24_measurePreserving_expOrderIso :
    MeasurePreserving Real.expOrderIso volume
      ccm24MultiplicativeHaarMeasure := by
  exact Real.expOrderIso.toHomeomorph.continuous.measurable.measurePreserving
    volume

theorem ccm24_measurePreserving_logOrderIso :
    MeasurePreserving Real.expOrderIso.symm
      ccm24MultiplicativeHaarMeasure volume :=
  MeasurePreserving.symm Real.expOrderIso.toHomeomorph.toMeasurableEquiv
    ccm24_measurePreserving_expOrderIso

/-- Pull a multiplicative-Haar `L2` function back along `rho = exp t`. -/
noncomputable def ccm24HaarToLogLinearMap :
    ccm24MultiplicativeHaarL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 :=
  Lp.compMeasurePreservingₗ ℂ Real.expOrderIso
    ccm24_measurePreserving_expOrderIso

/-- Push a logarithmic `L2` function to the multiplicative half-line through
`t = log rho`. -/
noncomputable def ccm24LogToHaarLinearMap :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] ccm24MultiplicativeHaarL2 :=
  Lp.compMeasurePreservingₗ ℂ Real.expOrderIso.symm
    ccm24_measurePreserving_logOrderIso

theorem ccm24HaarToLogLinearMap_coeFn
    (u : ccm24MultiplicativeHaarL2) :
    (ccm24HaarToLogLinearMap u : ℝ → ℂ) =ᵐ[volume]
      fun t => u (Real.expOrderIso t) :=
  Lp.coeFn_compMeasurePreserving u ccm24_measurePreserving_expOrderIso

theorem ccm24LogToHaarLinearMap_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (ccm24LogToHaarLinearMap u : CCM24PositiveReal → ℂ)
        =ᵐ[ccm24MultiplicativeHaarMeasure]
      fun rho => u (Real.expOrderIso.symm rho) :=
  Lp.coeFn_compMeasurePreserving u ccm24_measurePreserving_logOrderIso

theorem ccm24LogToHaar_leftInverse :
    Function.LeftInverse ccm24LogToHaarLinearMap ccm24HaarToLogLinearMap := by
  intro u
  rw [Lp.ext_iff]
  have hin :=
    ccm24_measurePreserving_logOrderIso.quasiMeasurePreserving.ae_eq
      (ccm24HaarToLogLinearMap_coeFn u)
  filter_upwards
    [ccm24LogToHaarLinearMap_coeFn (ccm24HaarToLogLinearMap u), hin] with
      rho hout hinAt
  rw [hout]
  simpa only [Function.comp_apply, Real.expOrderIso.apply_symm_apply]
    using hinAt

theorem ccm24LogToHaar_rightInverse :
    Function.RightInverse ccm24LogToHaarLinearMap ccm24HaarToLogLinearMap := by
  intro u
  rw [Lp.ext_iff]
  have hin :=
    ccm24_measurePreserving_expOrderIso.quasiMeasurePreserving.ae_eq
      (ccm24LogToHaarLinearMap_coeFn u)
  filter_upwards
    [ccm24HaarToLogLinearMap_coeFn (ccm24LogToHaarLinearMap u), hin] with
      t hout hinAt
  rw [hout]
  simpa only [Function.comp_apply, Real.expOrderIso.symm_apply_apply]
    using hinAt

/-- The canonical logarithmic realization
`L2(R_+^*, d rho / rho) ≃ L2(R, dt)`. -/
noncomputable def ccm24HaarLogEquiv :
    ccm24MultiplicativeHaarL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 where
  toLinearEquiv :=
    { toFun := ccm24HaarToLogLinearMap
      invFun := ccm24LogToHaarLinearMap
      left_inv := ccm24LogToHaar_leftInverse
      right_inv := ccm24LogToHaar_rightInverse
      map_add' := (ccm24HaarToLogLinearMap).map_add
      map_smul' := (ccm24HaarToLogLinearMap).map_smul }
  norm_map' := fun u =>
    Lp.norm_compMeasurePreserving u ccm24_measurePreserving_expOrderIso

theorem ccm24HaarLogEquiv_apply
    (u : ccm24MultiplicativeHaarL2) :
    ccm24HaarLogEquiv u = ccm24HaarToLogLinearMap u :=
  rfl

theorem ccm24HaarLogEquiv_symm_apply
    (u : cc20GlobalLogCrossingL2) :
    ccm24HaarLogEquiv.symm u = ccm24LogToHaarLinearMap u :=
  rfl

/-- The Plancherel Fourier transform of the multiplicative group
`R_+^*`, constructed on its actual Haar carrier. -/
noncomputable def ccm24MultiplicativeFourier :
    ccm24MultiplicativeHaarL2 ≃ₗᵢ[ℂ] ccm24MultiplicativeHaarL2 :=
  ccm24HaarLogEquiv.trans
    ((Lp.fourierTransformₗᵢ ℝ ℂ).trans ccm24HaarLogEquiv.symm)

/-- In logarithmic coordinates, the multiplicative Fourier transform is
exactly Mathlib's Plancherel Fourier transform. -/
theorem ccm24HaarLogEquiv_multiplicativeFourier
    (u : ccm24MultiplicativeHaarL2) :
    ccm24HaarLogEquiv (ccm24MultiplicativeFourier u) =
      Lp.fourierTransformₗᵢ ℝ ℂ (ccm24HaarLogEquiv u) := by
  simp [ccm24MultiplicativeFourier]

/-- The inverse multiplicative Fourier transform has the corresponding
inverse Plancherel readback. -/
theorem ccm24HaarLogEquiv_multiplicativeFourier_symm
    (u : ccm24MultiplicativeHaarL2) :
    ccm24HaarLogEquiv (ccm24MultiplicativeFourier.symm u) =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm (ccm24HaarLogEquiv u) := by
  simp [ccm24MultiplicativeFourier]

/-- The source half-density formula before passage to `L2` equivalence. -/
noncomputable def ccm24ArchimedeanHalfDensity
    (f : ℝ → ℂ) (rho : CCM24PositiveReal) : ℂ :=
  Real.sqrt rho.1 • f rho.1

theorem ccm24ArchimedeanHalfDensity_apply
    (f : ℝ → ℂ) (rho : CCM24PositiveReal) :
    ccm24ArchimedeanHalfDensity f rho =
      Real.sqrt rho.1 * f rho.1 := by
  simp [ccm24ArchimedeanHalfDensity]

/-- After logarithmic pullback, the half-density is exactly
`exp(t / 2) * f(exp t)`. -/
theorem ccm24ArchimedeanHalfDensity_exp
    (f : ℝ → ℂ) (t : ℝ) :
    ccm24ArchimedeanHalfDensity f (Real.expOrderIso t) =
      Real.exp (t / 2) * f (Real.exp t) := by
  rw [ccm24ArchimedeanHalfDensity_apply]
  simp only [Real.coe_expOrderIso_apply]
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 2
  ring_nf

end CC20Concrete
end Source
end ConnesWeilRH
