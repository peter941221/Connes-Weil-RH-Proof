/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24RadialHalfLineAlignment
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

/-!
# G8 P1 head-window energy lower bound (record 1330)

The full-carrier column-energy premise `hcolumn` (records 1324-1328) asks
that the antiresonant column `(primeEulerAmbientLossScale p : ℂ) •
(primeEulerAntiresonantCore p ∘L newSuffixFrame λ S)` have summable squared
basis norms.  The carrier is radial (`radialSupportProjection_comp_newSuffixFrame`):
its vectors vanish a.e. below `log lambda`.  The head window is the first
shift length `[log lambda, log lambda + log p)` of that half-line.  The
positive translation `U_(log p)` carries the head window strictly below the
half line, so antiperiodicity can never cancel the head-window part.

This leaf proves the sharp form:

```text
hcolumn  ⟹  Summable fun i =>
  ‖radialComplement (headWindowScale λ p)
    (newSuffixFrame λ S (newSuffixFrame λ S† (sourceBasis i)))‖²
```

i.e. summability of the carrier's head-window crossing energy, the
Hilbert-Schmidt content of `radialComplement (headWindowScale λ p) ∘ P_S`.
No vanishing statement, no sign of the projection defect, no `SourceRH`, and
no RH conclusion is proved or claimed here.  RH is not claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1HeadWindowEnergyLowerBound

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The head-window scale -/

/-- One `log p` displacement of the Sonin support scale: the head-window
cutoff `log lambda + log p = log (lambda * p)`. -/
noncomputable def headWindowScale
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) : CCM24SoninScale :=
  ⟨(lambda : ℝ) * (p : ℝ), by
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop
    exact mul_pos lambda.prop (zero_lt_one.trans hp)⟩

theorem log_headWindowScale
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    Real.log (headWindowScale lambda p) =
      Real.log lambda + Real.log p := by
  have hl : (lambda : ℝ) ≠ 0 := ne_of_gt lambda.prop
  have hp : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop
    linarith
  show Real.log ((lambda : ℝ) * (p : ℝ)) = Real.log lambda + Real.log p
  exact Real.log_mul hl hp

/-! ## Pointwise indicator readbacks -/

/-- The radial support projection is the half-line indicator
`[log mu, infinity)` almost everywhere. -/
theorem radialSupportProjection_coeFn_indicator
    (mu : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    (radialSupportProjection mu u : ℝ → ℂ) =ᵐ[volume]
      (Set.Ici (Real.log mu)).indicator (fun t => u t) := by
  show (ccm24LogRadialSupportProjection mu u : ℝ → ℂ) =ᵐ[volume]
      (Set.Ici (Real.log mu)).indicator (fun t => u t)
  rw [ccm24LogRadialSupportProjection_eq_translatedHalfLine]
  exact ccm24TranslatedHalfLineProjection_coeFn mu u

/-- The radial complement is the lower-window indicator
`(-infinity, log mu)` almost everywhere. -/
theorem radialComplement_coeFn_indicator
    (mu : CCM24SoninScale) (u : finiteSCarrier) :
    (radialComplement mu u : ℝ → ℂ) =ᵐ[volume]
      (Set.Iio (Real.log mu)).indicator (fun t => u t) := by
  have hP := radialSupportProjection_coeFn_indicator mu u
  have helem : radialComplement mu u =
      u - radialSupportProjection mu u := by
    simp only [radialComplement, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
  have hS := Lp.coeFn_sub u (radialSupportProjection mu u)
  have hS' : (radialComplement mu u : ℝ → ℂ) =ᵐ[volume]
      fun t => (u : ℝ → ℂ) t - (radialSupportProjection mu u : ℝ → ℂ) t := by
    rw [helem]
    exact hS
  filter_upwards [hP, hS'] with t eP ek
  rw [ek, eP]
  simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ici]
  by_cases ht : t < Real.log mu
  · rw [if_neg (by linarith : ¬(Real.log mu ≤ t)), if_pos ht]
    exact sub_zero _
  · have hge : Real.log mu ≤ t := by linarith
    rw [if_pos hge, if_neg (by linarith : ¬(t < Real.log mu))]
    exact sub_self _

/-! ## The head-window commutation -/

/-- The lower window of the base scale is exactly the `log p` preimage of the
lower window of the head scale: the radial complement intertwines the
positive translation with the translation of the complement at the shifted
scale. -/
theorem radialComplement_translation_commute
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap =
      (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
        radialComplement (headWindowScale lambda p) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext_iff.mpr
  have hhl := log_headWindowScale lambda p
  have eU : ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap f :
      ℝ → ℂ) =ᵐ[volume] fun t => (f : ℝ → ℂ) (t + Real.log p) :=
    cc20GlobalLogTranslation_coeFn (Real.log p) f
  -- LHS: complement at the base scale of the translated function
  have hlhs : ((radialComplement lambda ∘L
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap) f :
        ℝ → ℂ) =ᵐ[volume]
      (Set.Iio (Real.log lambda)).indicator
        (fun t => (f : ℝ → ℂ) (t + Real.log p)) := by
    have eP := radialComplement_coeFn_indicator lambda
      ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap f)
    filter_upwards [eP, eU] with t eP et
    rw [ContinuousLinearMap.comp_apply, eP]
    simp only [Set.indicator_apply]
    rw [et]
  -- RHS: translation of the complement at the head scale
  have hrhs : (((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
        radialComplement (headWindowScale lambda p)) f : ℝ → ℂ) =ᵐ[volume]
      (Set.Iio (Real.log lambda)).indicator
        (fun t => (f : ℝ → ℂ) (t + Real.log p)) := by
    have eP := radialComplement_coeFn_indicator (headWindowScale lambda p) f
    have eU2 : ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
          (radialComplement (headWindowScale lambda p) f) : ℝ → ℂ) =ᵐ[volume]
        fun t => (radialComplement (headWindowScale lambda p) f : ℝ → ℂ)
          (t + Real.log p) :=
      cc20GlobalLogTranslation_coeFn (Real.log p)
        (radialComplement (headWindowScale lambda p) f)
    have ePsh : (fun t => (radialComplement (headWindowScale lambda p) f :
        ℝ → ℂ) (t + Real.log p)) =ᵐ[volume]
        fun t => (Set.Iio (Real.log (headWindowScale lambda p))).indicator
          (fun s => (f : ℝ → ℂ) s) (t + Real.log p) :=
      (measurePreserving_add_right volume (Real.log p)).quasiMeasurePreserving.ae_eq eP
    have key : (fun t => (Set.Iio (Real.log (headWindowScale lambda p))).indicator
        (fun s => (f : ℝ → ℂ) s) (t + Real.log p)) =
        (Set.Iio (Real.log lambda)).indicator
          (fun t => (f : ℝ → ℂ) (t + Real.log p)) := by
      funext t
      show (Set.Iio (Real.log (headWindowScale lambda p))).indicator
          (fun s => (f : ℝ → ℂ) s) (t + Real.log p) = _
      simp only [Set.indicator_apply, Set.mem_Iio, hhl, add_lt_add_iff_right]
    rw [ContinuousLinearMap.comp_apply]
    refine eU2.trans (ePsh.trans (ae_of_all volume (fun x => congr_fun key x)))
  exact hlhs.trans hrhs.symm

/-! ## Pointwise head-window control of the antiresonant core -/

/-- The head-window part of a radial carrier vector is controlled by its
antiresonant core image: the first `log p` window of the half line cannot be
cancelled by `log p`-antiperiodicity, it can only be moved below the cutoff. -/
theorem norm_radialComplement_headWindow_le_norm_antiresonantCore
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {v : finiteSCarrier}
    (hfixed : radialSupportProjection lambda v = v) :
    ‖radialComplement (headWindowScale lambda p) v‖ ≤
      ‖primeEulerAntiresonantCore p v‖ := by
  have hcomm := DFunLike.congr_fun
    (radialComplement_translation_commute lambda p) v
  have hzero : radialComplement lambda v = 0 :=
    radialComplement_apply_eq_zero_of_fixed lambda hfixed
  have hcore : primeEulerAntiresonantCore p v =
      v + (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap v := by
    simp only [primeEulerAntiresonantCore, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply]
  calc ‖radialComplement (headWindowScale lambda p) v‖
      = ‖(cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
          (radialComplement (headWindowScale lambda p) v)‖ :=
        (norm_cc20GlobalLogTranslation (Real.log p) _).symm
    _ = ‖radialComplement lambda
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap v)‖ := by
        rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
          hcomm, ContinuousLinearMap.comp_apply]
    _ = ‖radialComplement lambda
          (v + (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap v)‖ := by
        rw [ContinuousLinearMap.map_add, hzero, zero_add]
    _ = ‖radialComplement lambda (primeEulerAntiresonantCore p v)‖ := by
        rw [← hcore]
    _ ≤ ‖radialComplement lambda‖ * ‖primeEulerAntiresonantCore p v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖primeEulerAntiresonantCore p v‖ :=
        mul_le_mul_of_nonneg_right (norm_radialComplement_le_one lambda)
          (norm_nonneg _)
    _ = ‖primeEulerAntiresonantCore p v‖ := one_mul _

/-! ## Energy transport from the column premise -/

/-- The carrier is radial pointwise on the actual new suffix frame. -/
theorem radialSupportProjection_newSuffixFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    radialSupportProjection lambda (newSuffixFrame lambda S x) =
      newSuffixFrame lambda S x :=
  DFunLike.congr_fun (radialSupportProjection_comp_newSuffixFrame lambda S) x

/-- Summability of the pulled-back antiresonant column energy transports to
summability of the head-window crossing energy of the carrier projection.
This is the sharp necessary condition extracted from `hcolumn`: the head
window of every carrier vector must have summable mass. -/
theorem summable_headWindowCrossing_normSq_of_antiresonantColumnEnergy
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (sourceBasis i))‖ ^ 2) :
    Summable fun i =>
      ‖radialComplement (headWindowScale unitSoninScale p)
        (newSuffixFrame unitSoninScale S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (sourceBasis i)))‖ ^ 2 := by
  have hcore : Summable fun i =>
      ‖primeEulerAntiresonantCore p
        (newSuffixFrame unitSoninScale S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (sourceBasis i)))‖ ^ 2 := by
    have hc0 : (primeEulerAmbientLossScale p : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (primeEulerAmbientLossScale_pos p)
    have hcn0 : ‖(primeEulerAmbientLossScale p : ℂ)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hc0
    have h2 : Summable fun i =>
        (‖(primeEulerAmbientLossScale p : ℂ)‖⁻¹ ^ 2) *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              (sourceBasis i))‖ ^ 2 := by
      simpa only [smul_eq_mul] using
        Summable.const_smul (‖(primeEulerAmbientLossScale p : ℂ)‖⁻¹ ^ 2) hcolumn
    refine Summable.congr h2 (fun i => ?_)
    have hcol := DFunLike.congr_fun
      (newFrameAntiresonantColumn_eq_scale_smul_core unitSoninScale p S)
      (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
        (sourceBasis i))
    calc (‖(primeEulerAmbientLossScale p : ℂ)‖⁻¹ ^ 2) *
            ‖newFrameAntiresonantColumn unitSoninScale p S
              (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                (sourceBasis i))‖ ^ 2
        = (‖(primeEulerAmbientLossScale p : ℂ)‖⁻¹ ^ 2) *
            ‖((primeEulerAmbientLossScale p : ℂ) •
              (primeEulerAntiresonantCore p
                (newSuffixFrame unitSoninScale S
                  (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                    (sourceBasis i)))))‖ ^ 2 := by
          rw [hcol]
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      _ = ‖primeEulerAntiresonantCore p
            (newSuffixFrame unitSoninScale S
              (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
                (sourceBasis i)))‖ ^ 2 := by
          rw [norm_smul, mul_pow]
          field_simp [hcn0]
  refine Summable.of_nonneg_of_le (hf := hcore) ?_ ?_
  · intro i
    exact sq_nonneg _
  · intro i
    have hfixed := radialSupportProjection_newSuffixFrame unitSoninScale S
      (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
        (sourceBasis i))
    have h := norm_radialComplement_headWindow_le_norm_antiresonantCore
      unitSoninScale p hfixed
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

end C1G8P1HeadWindowEnergyLowerBound
end Source
end ConnesWeilRH
