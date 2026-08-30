/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# C1: semilocal Hardy--Titchmarsh unitarity reduction

The finite-S transform is currently a bounded similarity

`H_S = T_S H_infinity T_S^{-1}`.

Its existing involution law alone does not make it unitary: a non-unitary
similarity of an involution need not preserve the Hilbert inner product.  The
F1' smoothing and root-commutator analysis needs the stronger Fourier-side
geometry, so this leaf isolates the exact missing route:

```text
H_infinity U_b = U_(-b) H_infinity
  -> H_infinity T_S = T_S^dagger H_infinity
  -> T_S normal
  -> H_S is self-adjoint and unitary.
```

This leaf now closes the finite-S algebraic part of that chain: the concrete
semilocal transform is self-adjoint, and its pre-existing involution law makes
the corresponding bounded-map geometry unitary.  It does not establish a
Hilbert--Schmidt or trace-class conclusion; F1' still requires its separate
continuum smoothing and signed-commutator proofs.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SemilocalHardyTitchmarshUnitarityReduction

open CC20Concrete
open CCM25Concrete.SelectedCrossingOperatorBridge
open MeasureTheory
open scoped ComplexConjugate ENNReal FourierTransform InnerProductSpace

local notation "H" => cc20GlobalLogCrossingL2

/-- The unit-modulus Fourier phase produced by translation by `b` in the
logarithmic coordinate. -/
noncomputable def spectralTranslationPhase (b xi : ℝ) : ℂ :=
  ((𝐞 (b * xi) : Circle) : ℂ)

theorem norm_spectralTranslationPhase (b xi : ℝ) :
    ‖spectralTranslationPhase b xi‖ = 1 := by
  simp only [spectralTranslationPhase, Circle.norm_coe]

theorem continuous_spectralTranslationPhase (b : ℝ) :
    Continuous (spectralTranslationPhase b) := by
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))

theorem memLp_spectralTranslationPhase (b : ℝ) :
    MemLp (spectralTranslationPhase b) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_spectralTranslationPhase b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun xi => by
      rw [norm_spectralTranslationPhase])

noncomputable def spectralTranslationPhaseLp (b : ℝ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_spectralTranslationPhase b).toLp (spectralTranslationPhase b)

theorem spectralTranslationPhaseLp_coeFn (b : ℝ) :
    (spectralTranslationPhaseLp b : ℝ → ℂ) =ᵐ[volume]
      spectralTranslationPhase b :=
  (memLp_spectralTranslationPhase b).coeFn_toLp

noncomputable def spectralTranslationPhaseInv (b xi : ℝ) : ℂ :=
  conj (spectralTranslationPhase b xi)

theorem continuous_spectralTranslationPhaseInv (b : ℝ) :
    Continuous (spectralTranslationPhaseInv b) := by
  exact Complex.continuous_conj.comp (continuous_spectralTranslationPhase b)

theorem memLp_spectralTranslationPhaseInv (b : ℝ) :
    MemLp (spectralTranslationPhaseInv b) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_spectralTranslationPhaseInv b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun xi => by
      rw [spectralTranslationPhaseInv, Complex.norm_conj,
        norm_spectralTranslationPhase])

noncomputable def spectralTranslationPhaseInvLp (b : ℝ) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_spectralTranslationPhaseInv b).toLp (spectralTranslationPhaseInv b)

theorem spectralTranslationPhaseInvLp_coeFn (b : ℝ) :
    (spectralTranslationPhaseInvLp b : ℝ → ℂ) =ᵐ[volume]
      spectralTranslationPhaseInv b :=
  (memLp_spectralTranslationPhaseInv b).coeFn_toLp

theorem spectralTranslationPhase_conj_mul (b xi : ℝ) :
    conj (spectralTranslationPhase b xi) * spectralTranslationPhase b xi = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    norm_spectralTranslationPhase]
  norm_num

theorem spectralTranslationPhase_mul_conj (b xi : ℝ) :
    spectralTranslationPhase b xi * conj (spectralTranslationPhase b xi) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    norm_spectralTranslationPhase]
  norm_num

noncomputable def spectralTranslationMultiplierLinearEquiv (b : ℝ) :
    H ≃ₗ[ℂ] H where
  toFun u := spectralTranslationPhaseLp b • u
  invFun u := spectralTranslationPhaseInvLp b • u
  left_inv u := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        (spectralTranslationPhaseInvLp b)
        (spectralTranslationPhaseLp b • u),
       Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        (spectralTranslationPhaseLp b) u,
       spectralTranslationPhaseLp_coeFn b,
       spectralTranslationPhaseInvLp_coeFn b] with
        xi hout hin hphase hphaseInv
    simp only [Pi.smul_apply'] at hout hin
    rw [hout, hin, hphase, hphaseInv]
    simp only [spectralTranslationPhaseInv, smul_eq_mul]
    rw [← mul_assoc, spectralTranslationPhase_conj_mul, one_mul]
  right_inv u := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        (spectralTranslationPhaseLp b)
        (spectralTranslationPhaseInvLp b • u),
       Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        (spectralTranslationPhaseInvLp b) u,
       spectralTranslationPhaseLp_coeFn b,
       spectralTranslationPhaseInvLp_coeFn b] with
        xi hout hin hphase hphaseInv
    simp only [Pi.smul_apply'] at hout hin
    rw [hout, hin, hphase, hphaseInv]
    simp only [spectralTranslationPhaseInv, smul_eq_mul]
    rw [← mul_assoc, spectralTranslationPhase_mul_conj, one_mul]
  map_add' u v := Lp.add_smul (spectralTranslationPhaseLp b) u v
  map_smul' c u := by
    exact (Lp.smul_comm (𝕜' := ℂ) (𝕜 := ℂ)
      (p := ∞) (q := 2) (r := 2) c
      (spectralTranslationPhaseLp b) u).symm

theorem norm_spectralTranslationMultiplierLinearEquiv
    (b : ℝ) (u : H) :
    ‖spectralTranslationMultiplierLinearEquiv b u‖ = ‖u‖ := by
  change ‖spectralTranslationPhaseLp b • u‖ = ‖u‖
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  filter_upwards
    [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralTranslationPhaseLp b) u,
     spectralTranslationPhaseLp_coeFn b] with xi hmul hphase
  rw [hmul, Pi.smul_apply', hphase, smul_eq_mul, norm_mul,
    norm_spectralTranslationPhase, one_mul]

/-- Fourier-side multiplication by the translation character. -/
noncomputable def spectralTranslationMultiplier (b : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := spectralTranslationMultiplierLinearEquiv b
  norm_map' := norm_spectralTranslationMultiplierLinearEquiv b

theorem spectralTranslationMultiplier_coeFn (b : ℝ) (u : H) :
    (spectralTranslationMultiplier b u : ℝ → ℂ) =ᵐ[volume]
      fun xi => spectralTranslationPhase b xi * u xi := by
  change ((spectralTranslationPhaseLp b • u : H) : ℝ → ℂ) =ᵐ[volume]
    fun xi => spectralTranslationPhase b xi * u xi
  filter_upwards
    [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralTranslationPhaseLp b) u,
     spectralTranslationPhaseLp_coeFn b] with xi hmul hphase
  rw [hmul, Pi.smul_apply', hphase, smul_eq_mul]

theorem spectralTranslationPhase_reflect (b xi : ℝ) :
    spectralTranslationPhase b (-xi) = spectralTranslationPhase (-b) xi := by
  unfold spectralTranslationPhase
  congr 2
  ring

/-- Spectral reflection flips the sign of a translation character. -/
theorem spectralReflection_comp_spectralTranslationMultiplier (b : ℝ) :
    (ccm24LogSpectralReflection : H →L[ℂ] H) ∘L
        (spectralTranslationMultiplier b : H →L[ℂ] H) =
      (spectralTranslationMultiplier (-b) : H →L[ℂ] H) ∘L
        (ccm24LogSpectralReflection : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  have hphaseNeg :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (spectralTranslationMultiplier_coeFn b u)
  filter_upwards
    [ccm24LogSpectralReflectionEquiv_coeFn (spectralTranslationMultiplier b u),
     hphaseNeg,
     spectralTranslationMultiplier_coeFn (-b) (ccm24LogSpectralReflection u),
     ccm24LogSpectralReflectionEquiv_coeFn u] with
      xi hleft hphaseNegAt hright hreflect
  change
    ((ccm24LogSpectralReflection
      (spectralTranslationMultiplier b u) : H) : ℝ → ℂ) xi =
      ((spectralTranslationMultiplier (-b)
        (ccm24LogSpectralReflection u) : H) : ℝ → ℂ) xi
  simp only [Function.comp_apply] at hphaseNegAt
  rw [hleft, hphaseNegAt, hright, hreflect]
  rw [spectralTranslationPhase_reflect]

/-- The scattering phase and a translation character are both Fourier-side
multipliers, hence commute exactly. -/
theorem scatteringMultiplier_comp_spectralTranslationMultiplier (b : ℝ) :
    (ccm24ArchimedeanScatteringMultiplier : H →L[ℂ] H) ∘L
        (spectralTranslationMultiplier b : H →L[ℂ] H) =
      (spectralTranslationMultiplier b : H →L[ℂ] H) ∘L
        (ccm24ArchimedeanScatteringMultiplier : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  filter_upwards
    [ccm24ArchimedeanScatteringMultiplier_coeFn
        (spectralTranslationMultiplier b u),
     spectralTranslationMultiplier_coeFn b u,
     spectralTranslationMultiplier_coeFn b
        (ccm24ArchimedeanScatteringMultiplier u),
     ccm24ArchimedeanScatteringMultiplier_coeFn u] with
      xi hleft hphase hright hscatter
  change
    ((ccm24ArchimedeanScatteringMultiplier
      (spectralTranslationMultiplier b u) : H) : ℝ → ℂ) xi =
      ((spectralTranslationMultiplier b
        (ccm24ArchimedeanScatteringMultiplier u) : H) : ℝ → ℂ) xi
  rw [hleft, hphase, hright, hscatter]
  ring

/-- On Schwartz functions, physical translation by `b` becomes multiplication
by the exact Fourier character.  This is the dense-core atom for the L2
translation law below. -/
theorem fourier_schwartz_translate (b : ℝ) (f : SchwartzMap ℝ ℂ) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ (-b) f) =
      fun xi : ℝ => 𝐞 (b * xi) • 𝓕 f xi := by
  have hshift :
      ((SchwartzMap.compSubConstCLM ℂ (-b) f : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
        (f : ℝ → ℂ) ∘ fun t : ℝ => t + b := by
    funext t
    simp only [SchwartzMap.compSubConstCLM_apply, Function.comp_apply]
    ring
  funext xi
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      ((SchwartzMap.compSubConstCLM ℂ (-b) f : SchwartzMap ℝ ℂ) : ℝ → ℂ) xi =
    𝐞 (b * xi) •
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (f : ℝ → ℂ) xi
  rw [hshift]
  have hpoint := congrFun
    (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℝ)
      (f : ℝ → ℂ) b) xi
  convert hpoint using 1
  congr 2
  rw [innerₗ_apply_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

set_option maxHeartbeats 800000 in
-- Three independently constructed `toLp` representatives must be normalized
-- under `Lp.ext_iff`; Mathlib's quotient elaboration exceeds the default cap.
/-- The `L2` Fourier isometry turns the concrete global log translation into
the spectral translation multiplier.  The proof extends the Schwartz identity
through the dense Schwartz range, rather than assuming an L1 representative
for an arbitrary L2 vector. -/
theorem fourierTransform_comp_globalLogTranslation
    (b : ℝ) (u : H) :
    Lp.fourierTransformₗᵢ ℝ ℂ (cc20GlobalLogTranslation b u) =
      spectralTranslationMultiplier b (Lp.fourierTransformₗᵢ ℝ ℂ u) := by
  let p : H → Prop := fun v =>
    Lp.fourierTransformₗᵢ ℝ ℂ (cc20GlobalLogTranslation b v) =
      spectralTranslationMultiplier b (Lp.fourierTransformₗᵢ ℝ ℂ v)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) u
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp
        (cc20GlobalLogTranslation b).continuous
    · exact (spectralTranslationMultiplier b).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro f
    change
      Lp.fourierTransformₗᵢ ℝ ℂ (cc20GlobalLogTranslation b (f.toLp 2)) =
        spectralTranslationMultiplier b (Lp.fourierTransformₗᵢ ℝ ℂ (f.toLp 2))
    have htranslation :
        cc20GlobalLogTranslation b (f.toLp 2) =
          (SchwartzMap.compSubConstCLM ℂ (-b) f).toLp 2 := by
      simpa only [neg_neg] using
        cc20GlobalLogTranslation_neg_apply_schwartzToLp f (-b)
    have hleft :
        Lp.fourierTransformₗᵢ ℝ ℂ
            ((SchwartzMap.compSubConstCLM ℂ (-b) f).toLp 2) =
          (𝓕 (SchwartzMap.compSubConstCLM ℂ (-b) f)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq (SchwartzMap.compSubConstCLM ℂ (-b) f)
    have hright :
        Lp.fourierTransformₗᵢ ℝ ℂ (f.toLp 2) = (𝓕 f).toLp 2 :=
      SchwartzMap.toLp_fourier_eq f
    rw [htranslation, hleft, hright]
    rw [Lp.ext_iff]
    filter_upwards
      [(𝓕 (SchwartzMap.compSubConstCLM ℂ (-b) f)).coeFn_toLp
         2 (volume : Measure ℝ),
       spectralTranslationMultiplier_coeFn b ((𝓕 f).toLp 2),
       (𝓕 f).coeFn_toLp 2 (volume : Measure ℝ)] with xi hleftAt hrightAt hfourAt
    rw [hleftAt, hrightAt, hfourAt]
    simpa only [spectralTranslationPhase, smul_eq_mul] using
      congrFun (fourier_schwartz_translate b f) xi

/-- The source Hardy--Titchmarsh transform reverses global logarithmic
translations.  This is the exact Fourier-side covariance that turns the
finite Euler transport into its adjoint under conjugation. -/
theorem archimedeanHardyTitchmarsh_globalLogTranslation
    (b : ℝ) (u : H) :
    ccm24ArchimedeanHardyTitchmarsh (cc20GlobalLogTranslation b u) =
      cc20GlobalLogTranslation (-b) (ccm24ArchimedeanHardyTitchmarsh u) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  have hreflect :
      ccm24LogSpectralReflection
          (spectralTranslationMultiplier b (Lp.fourierTransformₗᵢ ℝ ℂ u)) =
        spectralTranslationMultiplier (-b)
          (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u)) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : H →L[ℂ] H => T (Lp.fourierTransformₗᵢ ℝ ℂ u))
        (spectralReflection_comp_spectralTranslationMultiplier b)
  have hscatter :
      ccm24ArchimedeanScatteringMultiplier
          (spectralTranslationMultiplier (-b)
            (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u))) =
        spectralTranslationMultiplier (-b)
          (ccm24ArchimedeanScatteringMultiplier
            (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u))) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : H →L[ℂ] H => T
        (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u)))
        (scatteringMultiplier_comp_spectralTranslationMultiplier (-b))
  calc
    Lp.fourierTransformₗᵢ ℝ ℂ
        (ccm24ArchimedeanHardyTitchmarsh (cc20GlobalLogTranslation b u)) =
        ccm24ArchimedeanScatteringMultiplier
          (ccm24LogSpectralReflection
            (Lp.fourierTransformₗᵢ ℝ ℂ (cc20GlobalLogTranslation b u))) :=
      ccm24ArchimedeanHardyTitchmarsh_fourier_readback _
    _ = ccm24ArchimedeanScatteringMultiplier
          (ccm24LogSpectralReflection
            (spectralTranslationMultiplier b (Lp.fourierTransformₗᵢ ℝ ℂ u))) := by
      rw [fourierTransform_comp_globalLogTranslation b u]
    _ = ccm24ArchimedeanScatteringMultiplier
          (spectralTranslationMultiplier (-b)
            (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u))) := by
      rw [hreflect]
    _ = spectralTranslationMultiplier (-b)
          (ccm24ArchimedeanScatteringMultiplier
            (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u))) := hscatter
    _ = spectralTranslationMultiplier (-b)
          (Lp.fourierTransformₗᵢ ℝ ℂ (ccm24ArchimedeanHardyTitchmarsh u)) :=
      congrArg (spectralTranslationMultiplier (-b))
        (ccm24ArchimedeanHardyTitchmarsh_fourier_readback u).symm
    _ = Lp.fourierTransformₗᵢ ℝ ℂ
          (cc20GlobalLogTranslation (-b) (ccm24ArchimedeanHardyTitchmarsh u)) := by
      symm
      exact fourierTransform_comp_globalLogTranslation (-b)
        (ccm24ArchimedeanHardyTitchmarsh u)

/-- Operator form of the Hardy--Titchmarsh translation reversal. -/
theorem archimedeanHardyTitchmarsh_comp_globalLogTranslation (b : ℝ) :
    (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
        (cc20GlobalLogTranslation b).toContinuousLinearMap =
      (cc20GlobalLogTranslation (-b)).toContinuousLinearMap ∘L
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  exact archimedeanHardyTitchmarsh_globalLogTranslation b u

/-- The adjoint of one finite Euler factor reverses its logarithmic shift. -/
theorem ccm24PrimeEulerTransport_adjoint_eq (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint =
      1 - (ccm24PrimeEulerCoefficient p : ℂ) •
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap := by
  change (1 - ccm24PrimeEulerContraction p).adjoint = _
  change star (1 - ccm24PrimeEulerContraction p) = _
  rw [star_sub, star_one, ccm24PrimeEulerContraction, star_smul,
    ContinuousLinearMap.star_eq_adjoint,
    cc20GlobalLogTranslation_neg_adjoint (Real.log p)]
  simp

/-- The source Hardy--Titchmarsh transform takes one finite Euler factor to
its Hilbert adjoint. -/
theorem archimedeanHardyTitchmarsh_primeEulerTransport
    (p : CCM24VisiblePrime) (u : H) :
    ccm24ArchimedeanHardyTitchmarsh (ccm24PrimeEulerTransportEquiv p u) =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint
        (ccm24ArchimedeanHardyTitchmarsh u) := by
  rw [ccm24PrimeEulerTransportEquiv_apply,
    ccm24PrimeEulerTransport_adjoint_eq]
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply]
  rw [archimedeanHardyTitchmarsh_globalLogTranslation (-Real.log p) u]
  simp only [neg_neg]
  rfl

/-- Operator form of the one-prime Euler covariance. -/
theorem archimedeanHardyTitchmarsh_comp_primeEulerTransport
    (p : CCM24VisiblePrime) :
    (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint ∘L
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  exact archimedeanHardyTitchmarsh_primeEulerTransport p u

/-- The finite Euler transport is an ordered composition of its first prime
factor with the remaining list. -/
theorem ccm24FiniteEulerTransport_cons_toContinuousLinearMap
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv (p :: S)).toContinuousLinearMap =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply] using
    ccm24FiniteEulerTransportEquiv_cons_apply p S u

/-- The actual bounded maps of two individual Euler factors commute. -/
theorem ccm24PrimeEulerTransport_commute
    (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
      (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap := by
  change Commute (1 - ccm24PrimeEulerContraction p)
    (1 - ccm24PrimeEulerContraction q)
  exact ccm24PrimeEulerFactor_commute p q

/-- One Euler factor commutes with every finite product of such factors. -/
theorem ccm24PrimeEulerTransport_commute_finite
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
  let Tp : H →L[ℂ] H := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
  change Commute Tp (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      change Commute Tp (1 : H →L[ℂ] H)
      exact Commute.one_right _
  | cons q S ih =>
      rw [ccm24FiniteEulerTransport_cons_toContinuousLinearMap]
      let Tq : H →L[ℂ] H := (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap
      let TS : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
      change Commute Tp (Tq ∘L TS)
      change Commute Tp TS at ih
      have hpq : Commute Tp Tq := by
        dsimp only [Tp, Tq]
        exact ccm24PrimeEulerTransport_commute p q
      rw [Commute] at hpq ih ⊢
      change Tp * (Tq * TS) = (Tq * TS) * Tp
      calc
        Tp * (Tq * TS) = (Tp * Tq) * TS := (mul_assoc _ _ _).symm
        _ = (Tq * Tp) * TS := by rw [hpq]
        _ = Tq * (Tp * TS) := mul_assoc _ _ _
        _ = Tq * (TS * Tp) := by rw [ih]
        _ = (Tq * TS) * Tp := (mul_assoc _ _ _).symm

/-- Taking Hilbert adjoints preserves the finite-product commutation needed
to reverse the factor order. -/
theorem ccm24PrimeEulerTransport_adjoint_commute_finite
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap.adjoint
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint := by
  have hcomm := ccm24PrimeEulerTransport_commute_finite p S
  apply (commute_iff_eq _ _).2
  have hadj := congrArg (fun T : H →L[ℂ] H => star T) hcomm.eq
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint] using hadj.symm

/-- The source Hardy--Titchmarsh transform takes any finite Euler transport
to its Hilbert adjoint.  The proof uses the one-prime formula and then reverses
the finite product with the adjoint commutation lemma above. -/
theorem archimedeanHardyTitchmarsh_comp_finiteEulerTransport
    (S : List CCM24VisiblePrime) :
    (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      change (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
          ContinuousLinearMap.id ℂ H =
        (ContinuousLinearMap.id ℂ H).adjoint ∘L
          (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H)
      rw [ContinuousLinearMap.adjoint_id]
      simp
  | cons p S ih =>
      rw [ccm24FiniteEulerTransport_cons_toContinuousLinearMap]
      let Tp : H →L[ℂ] H := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
      let TS : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
      change (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L (Tp ∘L TS) =
        (Tp ∘L TS).adjoint ∘L (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H)
      have hprime :
          (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L Tp =
            Tp.adjoint ∘L (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
        dsimp only [Tp]
        exact archimedeanHardyTitchmarsh_comp_primeEulerTransport p
      have htail :
          (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L TS =
            TS.adjoint ∘L (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
        dsimp only [TS]
        exact ih
      have hadjcomm : Commute Tp.adjoint TS.adjoint := by
        dsimp only [Tp, TS]
        exact ccm24PrimeEulerTransport_adjoint_commute_finite p S
      have hadjcomm_comp : Tp.adjoint ∘L TS.adjoint = TS.adjoint ∘L Tp.adjoint := by
        apply ContinuousLinearMap.ext
        intro u
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply] using
          congrArg (fun T : H →L[ℂ] H => T u) hadjcomm.eq
      calc
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L (Tp ∘L TS) =
            ((ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L Tp) ∘L TS :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = (Tp.adjoint ∘L (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H)) ∘L TS := by
          rw [hprime]
        _ = Tp.adjoint ∘L
            ((ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L TS) :=
          ContinuousLinearMap.comp_assoc _ _ _
        _ = Tp.adjoint ∘L
            (TS.adjoint ∘L (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H)) := by
          rw [htail]
        _ = (Tp.adjoint ∘L TS.adjoint) ∘L
            (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = (TS.adjoint ∘L Tp.adjoint) ∘L
            (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
          rw [hadjcomm_comp]
        _ = (Tp ∘L TS).adjoint ∘L
            (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
          rw [ContinuousLinearMap.adjoint_comp]

/-- All global logarithmic translation maps commute, including shifts of
opposite sign. -/
theorem globalLogTranslation_toContinuousLinearMap_commute (a b : ℝ) :
    Commute (cc20GlobalLogTranslation a).toContinuousLinearMap
      (cc20GlobalLogTranslation b).toContinuousLinearMap := by
  apply (commute_iff_eq _ _).2
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.mul_apply] using
    cc20GlobalLogTranslation_commute a b u

/-- The adjoint of a prime Euler contraction has the opposite logarithmic
translation, with the same real Euler coefficient. -/
theorem ccm24PrimeEulerContraction_adjoint_eq (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerContraction p).adjoint =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap := by
  change star ((ccm24PrimeEulerCoefficient p : ℂ) •
    (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap) = _
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint,
    cc20GlobalLogTranslation_neg_adjoint (Real.log p)]
  simp

/-- A negative-shift Euler contraction commutes with the adjoint, hence
positive-shift, contraction at every finite place. -/
theorem ccm24PrimeEulerContraction_commute_adjoint
    (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerContraction p)
      (ccm24PrimeEulerContraction q).adjoint := by
  rw [ccm24PrimeEulerContraction_adjoint_eq]
  change Commute ((ccm24PrimeEulerCoefficient p : ℂ) •
      (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap)
    ((ccm24PrimeEulerCoefficient q : ℂ) •
      (cc20GlobalLogTranslation (Real.log q)).toContinuousLinearMap)
  exact
    ((globalLogTranslation_toContinuousLinearMap_commute
      (-Real.log p) (Real.log q)).smul_left _).smul_right _

/-- A prime Euler transport commutes with the adjoint of every other prime
Euler transport. -/
theorem ccm24PrimeEulerTransport_commute_adjoint
    (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
      (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap.adjoint := by
  change Commute (1 - ccm24PrimeEulerContraction p)
    (1 - ccm24PrimeEulerContraction q).adjoint
  have hcomm :
      Commute (1 - ccm24PrimeEulerContraction p)
        (1 - (ccm24PrimeEulerContraction q).adjoint) :=
    (Commute.one_left _).sub_left
      ((Commute.one_right _).sub_right
        (ccm24PrimeEulerContraction_commute_adjoint p q))
  simpa only [map_sub, ContinuousLinearMap.adjoint_one] using hcomm

/-- A finite Euler transport commutes with one adjointed prime factor. -/
theorem ccm24FiniteEulerTransport_commute_primeEulerTransport_adjoint
    (S : List CCM24VisiblePrime) (q : CCM24VisiblePrime) :
    Commute (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
      (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap.adjoint := by
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      change Commute (1 : H →L[ℂ] H)
        (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap.adjoint
      exact Commute.one_left _
  | cons p S ih =>
      rw [ccm24FiniteEulerTransport_cons_toContinuousLinearMap]
      change Commute
        ((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap *
          (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap)
        (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap.adjoint
      exact (ccm24PrimeEulerTransport_commute_adjoint p q).mul_left ih

/-- Every pair of finite Euler transports commutes after adjointing the
right-hand transport.  In particular, each finite transport is normal. -/
theorem ccm24FiniteEulerTransport_commute_adjoint
    (S T : List CCM24VisiblePrime) :
    Commute (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
      (ccm24FiniteEulerTransportEquiv T).toContinuousLinearMap.adjoint := by
  induction T with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      change Commute (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
        (ContinuousLinearMap.id ℂ H).adjoint
      rw [ContinuousLinearMap.adjoint_id]
      exact Commute.one_right _
  | cons q T ih =>
      rw [ccm24FiniteEulerTransport_cons_toContinuousLinearMap,
        ContinuousLinearMap.adjoint_comp]
      change Commute (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
        ((ccm24FiniteEulerTransportEquiv T).toContinuousLinearMap.adjoint *
          (ccm24PrimeEulerTransportEquiv q).toContinuousLinearMap.adjoint)
      exact ih.mul_right
        (ccm24FiniteEulerTransport_commute_primeEulerTransport_adjoint S q)

/-- Normality of the concrete finite Euler transport is now an exact
translation-algebra theorem, with no spectral or numerical premise. -/
theorem ccm24FiniteEulerTransport_isStarNormal (S : List CCM24VisiblePrime) :
    IsStarNormal (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
  refine ⟨?_⟩
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (ccm24FiniteEulerTransport_commute_adjoint S S).symm

/-- The inverse of the archimedean Hardy--Titchmarsh isometry is the same
operator, using its concrete involution law. -/
theorem archimedeanHardyTitchmarsh_symm_apply (u : H) :
    ccm24ArchimedeanHardyTitchmarsh.symm u =
      ccm24ArchimedeanHardyTitchmarsh u := by
  apply ccm24ArchimedeanHardyTitchmarsh.injective
  rw [ccm24ArchimedeanHardyTitchmarsh.apply_symm_apply,
    ccm24ArchimedeanHardyTitchmarsh_involutive]

/-- The concrete archimedean Hardy--Titchmarsh transform is self-adjoint on
the global logarithmic Hilbert carrier. -/
theorem archimedeanHardyTitchmarsh_adjoint_eq_self :
    (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H).adjoint =
      (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
  calc
    (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H).adjoint =
        (ccm24ArchimedeanHardyTitchmarsh.symm : H →L[ℂ] H) :=
      ccm24ArchimedeanHardyTitchmarsh.adjoint_eq_symm
    _ = (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
      apply ContinuousLinearMap.ext
      intro u
      exact archimedeanHardyTitchmarsh_symm_apply u

/-- The self-adjoint form of the source transform, ready for the finite Euler
transport conjugation calculation. -/
theorem archimedeanHardyTitchmarsh_isSelfAdjoint :
    IsSelfAdjoint (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact archimedeanHardyTitchmarsh_adjoint_eq_self

/-- The finite Euler transport and its inverse cancel as bounded maps.  This
is kept at the concrete equivalence boundary so later adjoint calculations do
not rely on a fictitious unitary structure for the transport itself. -/
theorem ccm24FiniteEulerTransport_comp_symm_toContinuousLinearMap
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap =
      (1 : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using
    (ccm24FiniteEulerTransportEquiv S).apply_symm_apply u

/-- The inverse finite Euler transport also cancels on the other side. -/
theorem ccm24FiniteEulerTransport_symm_comp_toContinuousLinearMap
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (1 : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using
    (ccm24FiniteEulerTransportEquiv S).symm_apply_apply u

/-- Taking Hilbert adjoints preserves the cancellation of the finite Euler
transport with its inverse. -/
theorem ccm24FiniteEulerTransport_symm_adjoint_comp_adjoint
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap.adjoint ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint =
      (1 : H →L[ℂ] H) := by
  calc
    (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap.adjoint ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint =
        ((ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
          (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp]
    _ = (1 : H →L[ℂ] H).adjoint := by
      rw [ccm24FiniteEulerTransport_comp_symm_toContinuousLinearMap]
    _ = 1 := ContinuousLinearMap.adjoint_one

/-- The finite Euler transport covariance extends to its inverse: after an
adjoint on the inverse, the source Hardy--Titchmarsh transform passes through
unchanged. -/
theorem ccm24FiniteEulerTransport_symm_adjoint_comp_archimedeanHardyTitchmarsh
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap.adjoint ∘L
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) =
      (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap := by
  let T : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Ti : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
  let Harch : H →L[ℂ] H := ccm24ArchimedeanHardyTitchmarsh
  change Ti.adjoint ∘L Harch = Harch ∘L Ti
  have hcov : Harch ∘L T = T.adjoint ∘L Harch := by
    dsimp only [T, Harch]
    exact archimedeanHardyTitchmarsh_comp_finiteEulerTransport S
  have hadj : Ti.adjoint ∘L T.adjoint = (1 : H →L[ℂ] H) := by
    dsimp only [T, Ti]
    exact ccm24FiniteEulerTransport_symm_adjoint_comp_adjoint S
  apply ContinuousLinearMap.ext
  intro u
  have htransport : T (Ti u) = u := by
    dsimp only [T, Ti]
    exact (ccm24FiniteEulerTransportEquiv S).apply_symm_apply u
  have hcov_point : Harch u = T.adjoint (Harch (Ti u)) := by
    simpa only [ContinuousLinearMap.comp_apply, htransport] using
      congrArg (fun operator : H →L[ℂ] H => operator (Ti u)) hcov
  calc
    Ti.adjoint (Harch u) = Ti.adjoint (T.adjoint (Harch (Ti u))) :=
      congrArg Ti.adjoint hcov_point
    _ = Harch (Ti u) := by
      change (Ti.adjoint ∘L T.adjoint) (Harch (Ti u)) = _
      rw [hadj]
      rfl

/-- Normality transports through the inverse: the inverse finite Euler map
commutes with the adjoint of the original finite Euler map. -/
theorem ccm24FiniteEulerTransport_symm_commute_adjoint
    (S : List CCM24VisiblePrime) :
    Commute (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint := by
  let T : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Ti : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
  change Commute Ti T.adjoint
  have hnormal : Commute T T.adjoint := by
    dsimp only [T]
    exact ccm24FiniteEulerTransport_commute_adjoint S S
  have htransport (u : H) : T (Ti u) = u := by
    dsimp only [T, Ti]
    exact (ccm24FiniteEulerTransportEquiv S).apply_symm_apply u
  apply (commute_iff_eq _ _).2
  apply ContinuousLinearMap.ext
  intro u
  change Ti (T.adjoint u) = T.adjoint (Ti u)
  apply (ccm24FiniteEulerTransportEquiv S).injective
  calc
    T (Ti (T.adjoint u)) = T.adjoint u := htransport _
    _ = T.adjoint (T (Ti u)) := congrArg T.adjoint (htransport u).symm
    _ = T (T.adjoint (Ti u)) :=
      (congrArg (fun operator : H →L[ℂ] H => operator (Ti u)) hnormal.eq).symm

/-- The companion form of the finite Euler covariance follows by applying the
source involution twice. -/
theorem ccm24FiniteEulerTransport_comp_archimedeanHardyTitchmarsh
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) =
      (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint := by
  let T : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Harch : H →L[ℂ] H := ccm24ArchimedeanHardyTitchmarsh
  change T ∘L Harch = Harch ∘L T.adjoint
  have hcov : Harch ∘L T = T.adjoint ∘L Harch := by
    dsimp only [T, Harch]
    exact archimedeanHardyTitchmarsh_comp_finiteEulerTransport S
  have hinvolutive (u : H) : Harch (Harch u) = u := by
    dsimp only [Harch]
    exact ccm24ArchimedeanHardyTitchmarsh_involutive u
  apply ContinuousLinearMap.ext
  intro u
  have hcov_point : Harch (T (Harch u)) = T.adjoint u := by
    simpa only [ContinuousLinearMap.comp_apply, hinvolutive] using
      congrArg (fun operator : H →L[ℂ] H => operator (Harch u)) hcov
  calc
    T (Harch u) = Harch (Harch (T (Harch u))) := (hinvolutive _).symm
    _ = Harch (T.adjoint u) := congrArg Harch hcov_point

/-- The concrete semilocal transform has the exact bounded-map factorization
`T_S H_infinity T_S⁻¹`. -/
theorem ccm24SemilocalHardyTitchmarsh_toContinuousLinearMap
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
      ((ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
          (ccm24ArchimedeanHardyTitchmarsh : H →L[ℂ] H)) ∘L
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The concrete finite-S Hardy--Titchmarsh transform is self-adjoint.  The
proof uses only the exact transport covariance, transport normality, and the
source involution; no asymptotic or numeric spectral premise is involved. -/
theorem ccm24SemilocalHardyTitchmarsh_adjoint_eq_self
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap.adjoint =
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap := by
  let T : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Ti : H →L[ℂ] H := (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
  let Harch : H →L[ℂ] H := ccm24ArchimedeanHardyTitchmarsh
  let HS : H →L[ℂ] H := (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap
  change HS.adjoint = HS
  have hfactor : HS = (T ∘L Harch) ∘L Ti := by
    dsimp only [HS, T, Harch, Ti]
    exact ccm24SemilocalHardyTitchmarsh_toContinuousLinearMap S
  have hinverse_cov : Ti.adjoint ∘L Harch = Harch ∘L Ti := by
    dsimp only [Ti, Harch]
    exact ccm24FiniteEulerTransport_symm_adjoint_comp_archimedeanHardyTitchmarsh S
  have hinverse_commutes : Commute Ti T.adjoint := by
    dsimp only [Ti, T]
    exact ccm24FiniteEulerTransport_symm_commute_adjoint S
  have hinverse_commutes_comp : Ti ∘L T.adjoint = T.adjoint ∘L Ti := by
    apply ContinuousLinearMap.ext
    intro u
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : H →L[ℂ] H => operator u) hinverse_commutes.eq
  have hreverse_cov : T ∘L Harch = Harch ∘L T.adjoint := by
    dsimp only [T, Harch]
    exact ccm24FiniteEulerTransport_comp_archimedeanHardyTitchmarsh S
  calc
    HS.adjoint = ((T ∘L Harch) ∘L Ti).adjoint := by rw [hfactor]
    _ = Ti.adjoint ∘L (T ∘L Harch).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp]
    _ = Ti.adjoint ∘L (Harch.adjoint ∘L T.adjoint) := by
      rw [ContinuousLinearMap.adjoint_comp]
    _ = (Ti.adjoint ∘L Harch) ∘L T.adjoint := by
      rw [archimedeanHardyTitchmarsh_adjoint_eq_self]
      exact (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (Harch ∘L Ti) ∘L T.adjoint := by rw [hinverse_cov]
    _ = Harch ∘L (Ti ∘L T.adjoint) :=
      ContinuousLinearMap.comp_assoc _ _ _
    _ = Harch ∘L (T.adjoint ∘L Ti) := by rw [hinverse_commutes_comp]
    _ = (Harch ∘L T.adjoint) ∘L Ti :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (T ∘L Harch) ∘L Ti := by rw [← hreverse_cov]
    _ = HS := hfactor.symm

/-- Self-adjoint formulation of the finite-S transform, available to the
projection geometry without assuming the Euler transport is itself unitary. -/
theorem ccm24SemilocalHardyTitchmarsh_isSelfAdjoint
    (S : List CCM24VisiblePrime) :
    IsSelfAdjoint (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact ccm24SemilocalHardyTitchmarsh_adjoint_eq_self S

/-- Operator form of the existing finite-S involution law. -/
theorem ccm24SemilocalHardyTitchmarsh_comp_self
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
        (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
      (1 : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using
    ccm24SemilocalHardyTitchmarsh_involutive S u

/-- The finite-S Hardy--Titchmarsh transform is a unitary bounded operator on
the common logarithmic Hilbert carrier. -/
theorem ccm24SemilocalHardyTitchmarsh_mem_unitary
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∈
      unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  constructor
  · change (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap.adjoint ∘L
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
        (1 : H →L[ℂ] H)
    rw [ccm24SemilocalHardyTitchmarsh_adjoint_eq_self]
    exact ccm24SemilocalHardyTitchmarsh_comp_self S
  · change (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap.adjoint =
        (1 : H →L[ℂ] H)
    rw [ccm24SemilocalHardyTitchmarsh_adjoint_eq_self]
    exact ccm24SemilocalHardyTitchmarsh_comp_self S

/-- The actual unitary owner of the finite-S Hardy--Titchmarsh transform. -/
noncomputable def ccm24SemilocalHardyTitchmarshUnitary
    (S : List CCM24VisiblePrime) :
    unitary (H →L[ℂ] H) :=
  ⟨(ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap,
    ccm24SemilocalHardyTitchmarsh_mem_unitary S⟩

/-- The same semilocal transform, now exposed as a linear isometric
equivalence for use with orthogonal-projection transport. -/
noncomputable def ccm24SemilocalHardyTitchmarshLinearIsometryEquiv
    (S : List CCM24VisiblePrime) : H ≃ₗᵢ[ℂ] H :=
  Unitary.linearIsometryEquiv (ccm24SemilocalHardyTitchmarshUnitary S)

theorem ccm24SemilocalHardyTitchmarshLinearIsometryEquiv_apply
    (S : List CCM24VisiblePrime) (u : H) :
    ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S u =
      ccm24SemilocalHardyTitchmarsh S u :=
  rfl

/-- Because the semilocal transform is an involution, its isometric inverse
has the same concrete action. -/
theorem ccm24SemilocalHardyTitchmarshLinearIsometryEquiv_symm_apply
    (S : List CCM24VisiblePrime) (u : H) :
    (ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).symm u =
      ccm24SemilocalHardyTitchmarsh S u := by
  apply (ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).injective
  calc
    ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S
        ((ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).symm u) = u :=
      (ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).apply_symm_apply u
    _ = ccm24SemilocalHardyTitchmarsh S
        (ccm24SemilocalHardyTitchmarsh S u) :=
      (ccm24SemilocalHardyTitchmarsh_involutive S u).symm
    _ = ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S
        (ccm24SemilocalHardyTitchmarsh S u) :=
      rfl

/-- The target Fourier-support subspace is literally the unitary image of the
radial-support subspace.  This replaces the old opaque comap geometry by the
concrete conjugation geometry needed for the F1' smoothing ledger. -/
theorem ccm24SemilocalFourierSupport_toSubmodule_eq_map_logRadialSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule =
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.map
        ((ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).toLinearEquiv :
          H →ₗ[ℂ] H) := by
  ext u
  constructor
  · intro hu
    change u ∈ ccm24SemilocalFourierSupportClosedSubspace lambda S at hu
    rw [mem_ccm24SemilocalFourierSupportClosedSubspace_iff] at hu
    refine ⟨ccm24SemilocalHardyTitchmarsh S u, hu, ?_⟩
    change ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S
        (ccm24SemilocalHardyTitchmarsh S u) = u
    rw [ccm24SemilocalHardyTitchmarshLinearIsometryEquiv_apply]
    exact ccm24SemilocalHardyTitchmarsh_involutive S u
  · rintro ⟨v, hv, hv_eq⟩
    change u ∈ ccm24SemilocalFourierSupportClosedSubspace lambda S
    rw [mem_ccm24SemilocalFourierSupportClosedSubspace_iff]
    rw [← hv_eq]
    change ccm24SemilocalHardyTitchmarsh S
        (ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S v) ∈
      ccm24LogRadialSupportClosedSubspace lambda
    rw [ccm24SemilocalHardyTitchmarshLinearIsometryEquiv_apply]
    simpa only [ccm24SemilocalHardyTitchmarsh_involutive] using hv

/-- Pointwise unitary-conjugation formula for the semilocal Fourier-support
projection. -/
theorem ccm24SemilocalFourierSupport_starProjection_apply
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (u : H) :
    (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection u =
      ccm24SemilocalHardyTitchmarsh S
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
          (ccm24SemilocalHardyTitchmarsh S u)) := by
  have hprojection :
      (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection =
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.map
          ((ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).toLinearEquiv :
            H →ₗ[ℂ] H)).starProjection :=
    Submodule.starProjection_inj.mpr
      (ccm24SemilocalFourierSupport_toSubmodule_eq_map_logRadialSupport lambda S)
  calc
    (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection u =
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.map
          ((ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).toLinearEquiv :
            H →ₗ[ℂ] H)).starProjection u :=
      congrArg (fun projection : H →L[ℂ] H => projection u) hprojection
    _ = ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S
          ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
            ((ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S).symm u)) :=
      Submodule.starProjection_map_apply
        (ccm24SemilocalHardyTitchmarshLinearIsometryEquiv S)
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule u
    _ = ccm24SemilocalHardyTitchmarsh S
        ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection
          (ccm24SemilocalHardyTitchmarsh S u)) := by
      rw [ccm24SemilocalHardyTitchmarshLinearIsometryEquiv_symm_apply]
      rfl

/-- Operator form of the target Fourier-support projection: it is the exact
unitary conjugate `H_S E H_S` of the half-line projection. -/
theorem ccm24SemilocalFourierSupport_starProjection_eq_unitary_conjugate
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection =
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
          (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply] using
    ccm24SemilocalFourierSupport_starProjection_apply lambda S u

end C1SemilocalHardyTitchmarshUnitarityReduction
end Source
end ConnesWeilRH
