/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperLift

/-!
# C1WindowTaperAssembly - the Young/convolution same-owner budget (N2beta component 4)

Contract 009 item 4 requires the Young bound to control the FINAL assembled
`CompactLogTest`, not an unrelated auxiliary interpolant.  This leaf delivers
exactly that:

- `compactLogL1`: the L1 accessor `f ↦ ∫ x, ‖f.test x‖` (finite on this
  class because every test is a continuous function with compact support);
- `integral_weighted_cauchySchwarz`: the full-measure weighted discriminant
  Cauchy-Schwarz `(∫ W b)² ≤ (∫ W)(∫ W b²)` for a nonnegative weight `W`;
- `young_kernel_sq_le`: the kernel Young inequality on the raw line —
  for continuous compactly supported `F G : ℝ → ℂ`,
  `∫ x, ‖∫ t, F t * G (x - t)‖² ≤ (∫ t, ‖F t‖)² * ∫ x, ‖G x‖²`, proved from
  the weighted Cauchy-Schwarz, Mathlib's `integral_convolution` (the
  packaged Fubini swap), and `HasCompactSupport.contDiff_convolution_right`;
  the boundedness of `‖G‖` uses `Continuous.bddAbove_range_of_hasCompactSupport`
  at the supremum `⨆ i, ‖G i‖`, so no support-window extraction is needed;
- `compactLogL2sq_convolution_le`: the same-owner budget law
  `compactLogL2sq (f.convolution g) ≤ compactLogL1 f ^ 2 * compactLogL2sq g`;
- `compactLogL1_sq_le_of_window`: `(∫ ‖u‖)² ≤ (d - c) * ∫ ‖u‖²` for a test
  supported in `Ioc c d`, by the record-1381 window Cauchy-Schwarz against
  the constant one;
- `exists_assembledOwner_cost_le`: the assembly.  Convolving ANY supported
  test `u` (supported in `Ioo c d`) with the record-1385 taper owner `f`
  (values `y`, cost `(1 + ε) · K_loc`) yields ONE owner `u.convolution f`
  whose support is the summed window, whose node values are
  `laplaceAt u (nodes i) * y i`, and whose squared L2 cost is at most
  `(d - c) * compactLogL2sq u * ((1 + ε) · K_loc)`.

No decay rate, no orbit instantiation, no numeric margin, no N3/N4/RH claim.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 4.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowTaperAssembly

open MeasureTheory
open scoped Topology
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinIndependence
open C1WindowTaperLift

/-! ### The L1 accessor and the nonnegativity facts -/

/-- The L1 norm of a compact log test: the full-line integral of the
pointwise norm. -/
noncomputable def compactLogL1 (f : CompactLogTest) : ℝ :=
  ∫ x : ℝ, ‖f.test x‖

/-- The squared L2 cost of a compact log test is nonnegative. -/
theorem compactLogL2sq_nonneg (f : CompactLogTest) :
    0 ≤ compactLogL2sq f :=
  integral_nonneg fun _x => sq_nonneg _

/-- The L1 cost of a compact log test is nonnegative. -/
theorem compactLogL1_nonneg (f : CompactLogTest) : 0 ≤ compactLogL1 f :=
  integral_nonneg fun _x => norm_nonneg _

/-! ### Weighted Cauchy-Schwarz on the full line -/

/-- The full-measure weighted Cauchy-Schwarz inequality by the discriminant
argument: for nonnegative `W` and arbitrary `b` with the three displayed
integrability hypotheses, `(∫ W b)² ≤ (∫ W)(∫ W b²)`.  The proof mirrors the record-1381
window argument with `∫ x in a..b` replaced by full integrals: the
positivity of `∫ W (b + s)²` for every `s : ℝ` expands (by `integral_add`
and `integral_smul`) to a quadratic in `s` with leading coefficient
`∫ W ≥ 0`; the leading-coefficient case `∫ W = 0` makes the quadratic
affine-nonnegative so the cross term vanishes, and the positive case is read
at the vertex `s = -(∫ W b)/(∫ W)`. -/
theorem integral_weighted_cauchySchwarz {W b : ℝ → ℝ} (hW0 : ∀ x, 0 ≤ W x)
    (hW : Integrable W volume)
    (hWb : Integrable (fun x => W x * b x) volume)
    (hWb2 : Integrable (fun x => W x * b x ^ 2) volume) :
    (∫ x : ℝ, W x * b x ∂volume) ^ 2 ≤
      (∫ x : ℝ, W x ∂volume) * (∫ x : ℝ, W x * b x ^ 2 ∂volume) := by
  have hR0 : 0 ≤ ∫ x : ℝ, W x ∂volume := integral_nonneg hW0
  have hP0 : 0 ≤ ∫ x : ℝ, W x * b x ^ 2 ∂volume :=
    integral_nonneg fun x => mul_nonneg (hW0 x) (sq_nonneg _)
  have hexpand : ∀ s : ℝ, ∫ x : ℝ, W x * (b x + s) ^ 2 ∂volume
      = (∫ x : ℝ, W x * b x ^ 2 ∂volume)
        + (2 * s) * (∫ x : ℝ, W x * b x ∂volume)
        + (s * s) * (∫ x : ℝ, W x ∂volume) := by
    intro s
    have hf : (fun x : ℝ => W x * (b x + s) ^ 2)
        = fun x : ℝ =>
          W x * b x ^ 2 + (2 * s) • (W x * b x) + (s * s) • W x := by
      funext x
      simp only [smul_eq_mul]
      ring
    have h1 : Integrable (fun x : ℝ => (2 * s) • (W x * b x)) volume :=
      ⟨hWb.aestronglyMeasurable.const_smul (2 * s),
        HasFiniteIntegral.smul (2 * s) hWb.hasFiniteIntegral⟩
    have h2 : Integrable (fun x : ℝ => (s * s) • W x) volume :=
      ⟨hW.aestronglyMeasurable.const_smul (s * s),
        HasFiniteIntegral.smul (s * s) hW.hasFiniteIntegral⟩
    have hsum : Integrable
        (fun x : ℝ => W x * b x ^ 2 + (2 * s) • (W x * b x)) volume :=
      hWb2.add h1
    rw [hf, integral_add hsum h2, integral_add hWb2 h1, integral_smul,
      integral_smul]
    simp only [smul_eq_mul]
  have hnonneg : ∀ s : ℝ, 0 ≤ (∫ x : ℝ, W x * b x ^ 2 ∂volume)
      + (2 * s) * (∫ x : ℝ, W x * b x ∂volume)
      + (s * s) * (∫ x : ℝ, W x ∂volume) := by
    intro s
    have h0 : 0 ≤ ∫ x : ℝ, W x * (b x + s) ^ 2 ∂volume :=
      integral_nonneg fun x => mul_nonneg (hW0 x) (sq_nonneg _)
    rw [hexpand s] at h0
    exact h0
  by_cases hR : (∫ x : ℝ, W x ∂volume) = 0
  · -- affine nonnegativity kills the cross term
    have hQ0 : (∫ x : ℝ, W x * b x ∂volume) = 0 := by
      by_contra hQ
      have h1 := hnonneg (-((∫ x : ℝ, W x * b x ^ 2 ∂volume) + 1)
        / (∫ x : ℝ, W x * b x ∂volume))
      rw [hR] at h1
      simp only [mul_zero, add_zero] at h1
      have h2 : (2 * (-((∫ x : ℝ, W x * b x ^ 2 ∂volume) + 1)
          / (∫ x : ℝ, W x * b x ∂volume)))
          * (∫ x : ℝ, W x * b x ∂volume)
          = -((2 : ℝ) * ((∫ x : ℝ, W x * b x ^ 2 ∂volume) + 1)) := by
        field_simp
      rw [h2] at h1
      linarith [hP0]
    rw [hQ0, hR]
    simp
  · -- the positive-leading-coefficient branch at the vertex
    have hRpos : 0 < ∫ x : ℝ, W x ∂volume :=
      lt_of_le_of_ne hR0 (Ne.symm hR)
    have h1 := hnonneg (-((∫ x : ℝ, W x * b x ∂volume)
      / (∫ x : ℝ, W x ∂volume)))
    have h2 : (((∫ x : ℝ, W x * b x ^ 2 ∂volume)
        + 2 * (-((∫ x : ℝ, W x * b x ∂volume) / (∫ x : ℝ, W x ∂volume)))
          * (∫ x : ℝ, W x * b x ∂volume))
        + (-((∫ x : ℝ, W x * b x ∂volume) / (∫ x : ℝ, W x ∂volume)))
          * (-((∫ x : ℝ, W x * b x ∂volume) / (∫ x : ℝ, W x ∂volume)))
          * (∫ x : ℝ, W x ∂volume))
      = (∫ x : ℝ, W x * b x ^ 2 ∂volume)
        - (∫ x : ℝ, W x * b x ∂volume) ^ 2 / (∫ x : ℝ, W x ∂volume) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (∫ x : ℝ, W x ∂volume)
        * ((∫ x : ℝ, W x * b x ∂volume) ^ 2 / (∫ x : ℝ, W x ∂volume))
        ≤ (∫ x : ℝ, W x ∂volume) * (∫ x : ℝ, W x * b x ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left (sub_nonneg.mp h1) hRpos.le
    have h4 : (∫ x : ℝ, W x ∂volume)
        * ((∫ x : ℝ, W x * b x ∂volume) ^ 2 / (∫ x : ℝ, W x ∂volume))
        = (∫ x : ℝ, W x * b x ∂volume) ^ 2 := by
      field_simp
    rw [h4] at h3
    exact h3

/-! ### The kernel Young inequality -/

/-- The kernel Young inequality `‖F ⋆ G‖₂² ≤ ‖F‖₁² · ‖G‖₂²` for continuous
compactly supported functions on the line, in raw pointwise form.  Pointwise
at `x`: the triangle bound followed by `integral_weighted_cauchySchwarz` at
the weight `t ↦ ‖F t‖` and `b = ‖G (x - ·)‖` gives
`‖∫ t, F t * G (x - t)‖² ≤ (∫ ‖F‖) * ∫ t, ‖F t‖ * ‖G (x - t)‖²`.  The right
side's inner integral is the REAL convolution of `‖F‖` against `‖G‖²`: it is
continuous and compactly supported, hence integrable, and `integral_mono`
pushes the pointwise bound to the line; the Fubini swap
`∫ x ∫ t = (∫ ‖F‖)(∫ ‖G‖²)` is Mathlib's `integral_convolution`. -/
theorem young_kernel_sq_le {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) :
    ∫ x : ℝ, ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2 ∂volume
      ≤ (∫ t : ℝ, ‖F t‖ ∂volume) ^ 2 * ∫ x : ℝ, ‖G x‖ ^ 2 ∂volume := by
  -- the weight and the squared modulus, with their integrability
  have hW0 : ∀ t : ℝ, 0 ≤ ‖F t‖ := fun t => norm_nonneg _
  have hWc : HasCompactSupport (fun t : ℝ => ‖F t‖) := hFc.norm
  have hWint : Integrable (fun t : ℝ => ‖F t‖) volume :=
    hF.norm.integrable_of_hasCompactSupport hWc
  have hGn : Continuous (fun x : ℝ => ‖G x‖) := hG.norm
  have hGcN : HasCompactSupport (fun x : ℝ => ‖G x‖) := hGc.norm
  have hGnint : Integrable (fun x : ℝ => ‖G x‖) volume :=
    hGn.integrable_of_hasCompactSupport hGcN
  have hM : BddAbove (Set.range (fun x : ℝ => ‖G x‖)) :=
    hGn.bddAbove_range_of_hasCompactSupport hGcN
  have hBcont : Continuous (fun y : ℝ => ‖G y‖ ^ 2) := hGn.pow 2
  have hBhc : HasCompactSupport (fun y : ℝ => ‖G y‖ ^ 2) := by
    show HasCompactSupport ((fun y : ℝ => y ^ 2) ∘ fun x : ℝ => ‖G x‖)
    exact hGcN.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hBint : Integrable (fun y : ℝ => ‖G y‖ ^ 2) volume := by
    have hgm : Integrable (fun y : ℝ => (⨆ i, ‖G i‖) * ‖G y‖) volume := by
      simpa using
        ⟨hGnint.aestronglyMeasurable.const_smul (⨆ i, ‖G i‖),
          HasFiniteIntegral.smul (⨆ i, ‖G i‖) hGnint.hasFiniteIntegral⟩
    refine Integrable.mono' hgm hBcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle : ‖G y‖ ^ 2 ≤ (⨆ i, ‖G i‖) * ‖G y‖ := by
      have h : ‖G y‖ * ‖G y‖ ≤ (⨆ i, ‖G i‖) * ‖G y‖ :=
        mul_le_mul_of_nonneg_right (le_ciSup hM y) (norm_nonneg _)
      simpa [pow_two] using h
    exact hle
  -- pointwise Young bound
  have hpt : ∀ x : ℝ, ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2
      ≤ (∫ t : ℝ, ‖F t‖ ∂volume) * ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2 ∂volume := by
    intro x
    have hbcont : Continuous (fun t : ℝ => ‖G (x - t)‖) :=
      hGn.comp (continuous_const.sub continuous_id)
    have hWb : Integrable (fun t : ℝ => ‖F t‖ * ‖G (x - t)‖) volume := by
      have hgm : Integrable (fun t : ℝ => (⨆ i, ‖G i‖) * ‖F t‖) volume := by
        simpa using
          ⟨hWint.aestronglyMeasurable.const_smul (⨆ i, ‖G i‖),
            HasFiniteIntegral.smul (⨆ i, ‖G i‖) hWint.hasFiniteIntegral⟩
      refine Integrable.mono' hgm (hF.norm.mul hbcont).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [mul_comm (⨆ i, ‖G i‖)]
      exact mul_le_mul_of_nonneg_left (le_ciSup hM (x - t)) (norm_nonneg _)
    have hWb2 : Integrable (fun t : ℝ => ‖F t‖ * ‖G (x - t)‖ ^ 2) volume := by
      have hgm : Integrable
          (fun t : ℝ => (⨆ i, ‖G i‖) * (‖F t‖ * ‖G (x - t)‖)) volume := by
        simpa using
          ⟨(hF.norm.mul hbcont).aestronglyMeasurable.const_smul (⨆ i, ‖G i‖),
            HasFiniteIntegral.smul (⨆ i, ‖G i‖) hWb.hasFiniteIntegral⟩
      refine Integrable.mono' hgm
        (hF.norm.mul (hbcont.pow 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
      have hb : ‖G (x - t)‖ ≤ ⨆ i, ‖G i‖ := le_ciSup hM (x - t)
      have hb2 : ‖G (x - t)‖ ^ 2 ≤ (⨆ i, ‖G i‖) * ‖G (x - t)‖ := by
        have h2 : ‖G (x - t)‖ * ‖G (x - t)‖ ≤ (⨆ i, ‖G i‖) * ‖G (x - t)‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        simpa [pow_two] using h2
      calc ‖F t‖ * ‖G (x - t)‖ ^ 2
          ≤ ‖F t‖ * ((⨆ i, ‖G i‖) * ‖G (x - t)‖) :=
            mul_le_mul_of_nonneg_left hb2 (norm_nonneg _)
        _ = (⨆ i, ‖G i‖) * (‖F t‖ * ‖G (x - t)‖) := by ring
    have hcs := integral_weighted_cauchySchwarz hW0 hWint hWb hWb2
    have htri : ‖∫ t : ℝ, F t * G (x - t)‖
        ≤ ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ∂volume :=
      (norm_integral_le_integral_norm
          (f := fun t : ℝ => F t * G (x - t))).trans
        (le_of_eq (integral_congr_ae
          (Filter.Eventually.of_forall
            fun t => show ‖F t * G (x - t)‖ = ‖F t‖ * ‖G (x - t)‖
              from norm_mul (F t) (G (x - t)))))
    have hn : 0 ≤ ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ∂volume :=
      integral_nonneg fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2
        ≤ (∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ∂volume) ^ 2 := by
      nlinarith [htri, hn, norm_nonneg (∫ t : ℝ, F t * G (x - t))]
    exact hsq.trans hcs
  -- the raw complex convolution: continuous, compactly supported
  have hFint : Integrable F volume := hF.integrable_of_hasCompactSupport hFc
  have hconv_eq : (fun x : ℝ => ∫ t : ℝ, F t * G (x - t))
      = MeasureTheory.convolution F G (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x
    unfold MeasureTheory.convolution
    simp only [ContinuousLinearMap.mul_apply']
  have hconvcont : Continuous (fun x : ℝ => ∫ t : ℝ, F t * G (x - t)) := by
    rw [hconv_eq]
    exact contDiff_zero.mp
      (hGc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) (n := 0)
        hFint.locallyIntegrable (contDiff_zero.mpr hG))
  have hconvhc : HasCompactSupport (fun x : ℝ => ∫ t : ℝ, F t * G (x - t)) := by
    rw [hconv_eq]
    exact hFc.convolution (ContinuousLinearMap.mul ℝ ℂ) hGc
  have hminorint : Integrable (fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2)
      volume := by
    have hc : Continuous (fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖) :=
      hconvcont.norm
    have hh : HasCompactSupport (fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖) :=
      hconvhc.norm
    have hp : Continuous (fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2) :=
      hc.pow 2
    have hhp : HasCompactSupport
        (fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2) := by
      show HasCompactSupport
        ((fun y : ℝ => y ^ 2) ∘ fun x : ℝ => ‖∫ t : ℝ, F t * G (x - t)‖)
      exact hh.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact hp.integrable_of_hasCompactSupport hhp
  -- the real majorant convolution: pointwise the inner integral, and
  -- continuous / compactly supported / integrable
  have hJ_eq : (fun x : ℝ => ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2)
      = MeasureTheory.convolution (fun t : ℝ => ‖F t‖)
        (fun y : ℝ => ‖G y‖ ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    unfold MeasureTheory.convolution
    simp only [ContinuousLinearMap.mul_apply']
  have hJcont : Continuous (fun x : ℝ => ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2) := by
    rw [hJ_eq]
    exact contDiff_zero.mp
      (hBhc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) (n := 0)
        hWint.locallyIntegrable (contDiff_zero.mpr hBcont))
  have hJhc : HasCompactSupport
      (fun x : ℝ => ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2) := by
    rw [hJ_eq]
    exact hWc.convolution (ContinuousLinearMap.mul ℝ ℝ) hBhc
  have hJint : Integrable (fun x : ℝ => ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2)
      volume := hJcont.integrable_of_hasCompactSupport hJhc
  have hRmaj : Integrable
      (fun x : ℝ => (∫ t : ℝ, ‖F t‖ ∂volume)
        * ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2 ∂volume) volume := by
    simpa using
      ⟨hJint.aestronglyMeasurable.const_smul (∫ t : ℝ, ‖F t‖ ∂volume),
        HasFiniteIntegral.smul (∫ t : ℝ, ‖F t‖ ∂volume)
          hJint.hasFiniteIntegral⟩
  have hswap : ∫ x : ℝ, ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2 ∂volume ∂volume
      = (∫ t : ℝ, ‖F t‖ ∂volume) * ∫ x : ℝ, ‖G x‖ ^ 2 ∂volume := by
    rw [hJ_eq]
    simpa only [ContinuousLinearMap.mul_apply'] using
      (integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hWint hBint)
  calc ∫ x : ℝ, ‖∫ t : ℝ, F t * G (x - t)‖ ^ 2 ∂volume
      ≤ ∫ x : ℝ, (∫ t : ℝ, ‖F t‖ ∂volume)
          * ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2 ∂volume ∂volume := by
        exact integral_mono hminorint hRmaj fun x => hpt x
    _ = (∫ t : ℝ, ‖F t‖ ∂volume) • ∫ x : ℝ,
          ∫ t : ℝ, ‖F t‖ * ‖G (x - t)‖ ^ 2 ∂volume ∂volume := by
        simp only [← smul_eq_mul, integral_smul]
    _ = (∫ t : ℝ, ‖F t‖ ∂volume) • ((∫ t : ℝ, ‖F t‖ ∂volume)
        * ∫ x : ℝ, ‖G x‖ ^ 2 ∂volume) := by rw [hswap]
    _ = (∫ t : ℝ, ‖F t‖ ∂volume) ^ 2 * ∫ x : ℝ, ‖G x‖ ^ 2 ∂volume := by
        rw [smul_eq_mul]
        ring

/-! ### Same-owner budget laws on the CompactLog owner -/

/-- The record-1381 window Cauchy-Schwarz against the constant one turns the
L1 mass of a window-supported test into width times squared L2 cost. -/
theorem compactLogL1_sq_le_of_window (f : CompactLogTest) {c d : ℝ}
    (hcd : c ≤ d) (hsupp : Function.support f.test ⊆ Set.Ioc c d) :
    compactLogL1 f ^ 2 ≤ (d - c) * compactLogL2sq f := by
  have hsuppN : Function.support (fun x : ℝ => ‖f.test x‖) ⊆ Set.Ioc c d := by
    intro x hx
    exact hsupp (by simpa using hx)
  have hsuppN2 : Function.support (fun x : ℝ => ‖f.test x‖ ^ 2)
      ⊆ Set.Ioc c d := by
    intro x hx
    exact hsupp (by simpa using hx)
  have hL1 : compactLogL1 f = ∫ x : ℝ in c..d, ‖f.test x‖ ∂volume := by
    rw [compactLogL1]
    exact (intervalIntegral.integral_eq_integral_of_support_subset hsuppN).symm
  have hL2 : compactLogL2sq f = ∫ x : ℝ in c..d, ‖f.test x‖ ^ 2 ∂volume := by
    rw [compactLogL2sq]
    exact (intervalIntegral.integral_eq_integral_of_support_subset hsuppN2).symm
  have hcs := intervalIntegral_cauchySchwarz
    (u := fun x : ℝ => ‖f.test x‖) (v := fun _ : ℝ => (1 : ℝ)) hcd
    (f.test.continuous.norm.continuousOn) continuous_const.continuousOn
  have hmul : ∫ x : ℝ in c..d, ‖f.test x‖ * (1 : ℝ) ∂volume
      = ∫ x : ℝ in c..d, ‖f.test x‖ ∂volume :=
    intervalIntegral.integral_congr fun x _ => mul_one _
  have hone : ∫ x : ℝ in c..d, (1 : ℝ) ^ 2 ∂volume = d - c := by
    have h : ∫ x : ℝ in c..d, (1 : ℝ) ^ 2 ∂volume
        = (d - c) • (1 : ℝ) ^ 2 := intervalIntegral.integral_const ((1 : ℝ) ^ 2)
    rw [h]
    simp
  calc compactLogL1 f ^ 2
      = (∫ x : ℝ in c..d, ‖f.test x‖ ∂volume) ^ 2 := by rw [hL1]
    _ ≤ (∫ x : ℝ in c..d, ‖f.test x‖ ^ 2 ∂volume) * (d - c) := by
        rw [← hmul, ← hone]
        exact hcs
    _ = (d - c) * compactLogL2sq f := by rw [hL2, mul_comm]

/-- The same-owner Young budget: convolving a compact log test `f` on the
left costs at most `compactLogL1 f ^ 2 * compactLogL2sq g`. -/
theorem compactLogL2sq_convolution_le (f g : CompactLogTest) :
    compactLogL2sq (f.convolution g) ≤
      compactLogL1 f ^ 2 * compactLogL2sq g := by
  have key := young_kernel_sq_le f.test.continuous g.test.continuous
    f.compactSupport g.compactSupport
  calc compactLogL2sq (f.convolution g)
      = ∫ x : ℝ, ‖(f.convolution g).test x‖ ^ 2 ∂volume := rfl
    _ = ∫ x : ℝ, ‖∫ t : ℝ, f.test t * g.test (x - t)‖ ^ 2 ∂volume := rfl
    _ ≤ (∫ t : ℝ, ‖f.test t‖ ∂volume) ^ 2 * ∫ x : ℝ, ‖g.test x‖ ^ 2 ∂volume :=
        key
    _ = compactLogL1 f ^ 2 * compactLogL2sq g := by
        simp only [compactLogL1, compactLogL2sq]

/-- The windowed form of the same-owner Young budget: the L1 factor is
itself traded for width times squared L2 cost. -/
theorem compactLogL2sq_convolution_le_of_window (u f : CompactLogTest)
    {c d : ℝ} (hcd : c < d)
    (hsupp : Function.support u.test ⊆ Set.Ioo c d) :
    compactLogL2sq (u.convolution f) ≤
      (d - c) * compactLogL2sq u * compactLogL2sq f := by
  have hIoc : Function.support u.test ⊆ Set.Ioc c d :=
    hsupp.trans Set.Ioo_subset_Ioc_self
  calc compactLogL2sq (u.convolution f)
      ≤ compactLogL1 u ^ 2 * compactLogL2sq f :=
        compactLogL2sq_convolution_le u f
    _ ≤ (d - c) * compactLogL2sq u * compactLogL2sq f :=
        mul_le_mul_of_nonneg_right
          (compactLogL1_sq_le_of_window u hcd.le hIoc)
          (compactLogL2sq_nonneg f)

/-! ### The assembly deliverable -/

/-- Contract 009 item 4, the assembly: convolving any window-supported test
`u` with the record-1385 taper owner `f` produces ONE owner `g` living in the
summed window, realizing the values `laplaceAt u (nodes i) * y i` at every
node, with the machine-checked budget
`compactLogL2sq g ≤ (d - c) * compactLogL2sq u * ((1 + ε) * K_loc)` for the
record-1379 constant `K_loc = y* G⁻¹ y`.  The convolution law
`laplaceAt_convolution` supplies the values, the record-CC20 support addition
law supplies the window, and the Young budget of this leaf supplies the
cost.  No orbit, no numeric margin, no N3/N4/RH claim. -/
theorem exists_assembledOwner_cost_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ)
    (u : CompactLogTest) (hu : Function.support u.test ⊆ Set.Ioo c d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CompactLogTest,
      Function.support g.test ⊆ Set.Ioo (c + a) (d + b) ∧
        (∀ i : ι, laplaceAt g (nodes i) = laplaceAt u (nodes i) * y i) ∧
        compactLogL2sq g ≤ (d - c) * compactLogL2sq u *
          ((1 + ε) * (dotProduct (star (Matrix.mulVec
              ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹
              y)) y).re) := by
  obtain ⟨f, hfsp, hfval, hfcost⟩ :=
    exists_windowTaperCorrection_cost_le_one_plus_eps hab nodes hne y hε
  refine ⟨u.convolution f, ?_, ?_, ?_⟩
  · exact convolution_support_subset_add_Ioo u f hu hfsp
  · intro i
    rw [laplaceAt_convolution, hfval]
  · have hW : 0 ≤ (d - c) * compactLogL2sq u :=
      mul_nonneg (sub_nonneg.mpr hcd.le) (compactLogL2sq_nonneg u)
    calc compactLogL2sq (u.convolution f)
        ≤ (d - c) * compactLogL2sq u * compactLogL2sq f :=
          compactLogL2sq_convolution_le_of_window u f hcd hu
      _ ≤ (d - c) * compactLogL2sq u
          * ((1 + ε) * (dotProduct (star (Matrix.mulVec
              ↑(windowExpGramMatrix_isUnit_of_injective hab nodes
                hne).unit⁻¹ y)) y).re) :=
          mul_le_mul_of_nonneg_left hfcost hW

end C1WindowTaperAssembly
end Source
end ConnesWeilRH
