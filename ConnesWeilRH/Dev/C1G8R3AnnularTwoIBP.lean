/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import ConnesWeilRH.Dev.C1G8R3AnnularTailDecay

/-!
# Two integrations by parts: the oscillatory-decay face of the θ-page

Record 1735.  Record 1734 section 4 prices the fixed tail of the
Hardy-transformed kernel by two integrations by parts: if `θ, θ', θ''` are
integrable and `v(s) = ∫ θ(ξ) e^{-2πiξs} dξ`, then
`|v(s)| ≤ ‖θ''‖₁ / (4π² s²)`.  This leaf lands that face formally:

1. `abs_osci_integral_le_of_C2` — the two-IBP decay itself, using Mathlib's
   whole-line integration-by-parts lemma
   `integral_mul_deriv_eq_deriv_mul_of_integrable` (with the product
   integrable there are no boundary terms, which is exactly our situation
   since the exponential has modulus one and `θ` is `L¹`);
2. `annular_v_tail_lintegral_le_of_two_ibp` — the composition with the
   record-1734 weighted moment leaf, giving the exact `‖θ''‖₁²/(32π⁴X²)`
   constant of record 1734 section 4.

No carrier object, no root convolution, and no sign is touched here.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Complex
open scoped Real

section TwoIBP

/-- The oscillatory factor has modulus one. -/
private theorem norm_osci_exp_eq_one (s ξ : ℝ) :
    ‖cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))‖ = 1 := by
  have hz : ((ξ : ℂ) * (ofReal (-2 * π * s) * I))
      = ofReal (-2 * π * s * ξ) * I := by
    push_cast
    ring
  rw [hz, Complex.norm_exp_ofReal_mul_I]

/-- The oscillatory factor's derivative. -/
private theorem hasDerivAt_osci_exp (s ξ : ℝ) :
    HasDerivAt (fun t : ℝ => cexp ((t : ℂ) * (ofReal (-2 * π * s) * I)))
      (cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))
        * (ofReal (-2 * π * s) * I)) ξ := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 ξ :=
    Complex.ofRealCLM.hasDerivAt
  have hinner := hid.mul_const (ofReal (-2 * π * s) * I)
  rw [one_mul] at hinner
  have houter := Complex.hasDerivAt_exp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))
  exact houter.comp ξ hinner

/-- **Two integrations by parts** (record 1734 section 4).  For `θ, θ', θ''`
integrable with the two derivative relations, the oscillatory integral of
`θ` at frequency `s ≠ 0` decays like `‖θ''‖₁ / (4π² s²)`. -/
theorem abs_osci_integral_le_of_C2
    {θ θ' θ'' : ℝ → ℂ} {s : ℝ} (hs : s ≠ 0)
    (h1 : ∀ ξ : ℝ, HasDerivAt θ (θ' ξ) ξ)
    (h2 : ∀ ξ : ℝ, HasDerivAt θ' (θ'' ξ) ξ)
    (hθ1 : Integrable (fun ξ : ℝ => θ ξ) volume)
    (hθ2 : Integrable (fun ξ : ℝ => θ' ξ) volume)
    (hθ3 : Integrable (fun ξ : ℝ => θ'' ξ) volume) :
    ‖∫ ξ : ℝ, θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))‖
      ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2 * s ^ 2) := by
  set c : ℂ := ofReal (-2 * π * s) * I with hc
  set E : ℝ → ℂ := fun t => cexp ((t : ℂ) * c) with hE
  set E' : ℝ → ℂ := fun t => E t * c with hE'
  -- derivative and integrability of the pieces
  have hEd : ∀ ξ : ℝ, HasDerivAt E (E' ξ) ξ := by
    intro ξ
    have hd := hasDerivAt_osci_exp s ξ
    simp only [hE, hE', hc]
    exact hd
  have hEnorm : ∀ ξ : ℝ, ‖E ξ‖ = 1 := by
    intro ξ
    rw [hE]
    exact norm_osci_exp_eq_one s ξ
  have hI1 : ‖I‖ = 1 := by
    have h2 : ‖I‖ * ‖I‖ = ‖I * I‖ := (norm_mul I I).symm
    rw [Complex.I_mul_I, norm_neg, norm_one] at h2
    nlinarith [norm_nonneg I]
  have hcnorm : ‖c‖ = 2 * π * |s| := by
    rw [hc, norm_mul, hI1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_neg,
      abs_of_pos (show (0:ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
  have hE'norm : ∀ ξ : ℝ, ‖E' ξ‖ = 2 * π * |s| := by
    intro ξ
    rw [hE', norm_mul, hEnorm ξ, one_mul, hcnorm]
  have hmeasE : AEStronglyMeasurable E volume := by measurability
  have hintE : Integrable (fun ξ : ℝ => θ ξ * E ξ) :=
    hθ1.mono (hθ1.aestronglyMeasurable.mul hmeasE)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul, hEnorm ξ, mul_one])
  have hintθ'E : Integrable (fun ξ : ℝ => θ' ξ * E ξ) :=
    hθ2.mono (hθ2.aestronglyMeasurable.mul hmeasE)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul, hEnorm ξ, mul_one])
  have hintθ''E : Integrable (fun ξ : ℝ => θ'' ξ * E ξ) :=
    hθ3.mono (hθ3.aestronglyMeasurable.mul hmeasE)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul, hEnorm ξ, mul_one])
  have hintE' : Integrable (fun ξ : ℝ => θ ξ * E' ξ) := by
    have hEq : (fun ξ : ℝ => θ ξ * E' ξ) = fun ξ : ℝ => c * (θ ξ * E ξ) := by
      funext ξ
      rw [hE']
      ring
    rw [hEq]
    exact hintE.const_mul c
  have hintE'θ : Integrable (fun ξ : ℝ => θ' ξ * E' ξ) := by
    have hEq : (fun ξ : ℝ => θ' ξ * E' ξ) = fun ξ : ℝ => c * (θ' ξ * E ξ) := by
      funext ξ
      rw [hE']
      ring
    rw [hEq]
    exact hintθ'E.const_mul c
  -- IBP 1 and IBP 2 (whole-line, no boundary terms)
  have hIBP1 : (∫ ξ : ℝ, θ ξ * E' ξ)
      = -(∫ ξ : ℝ, θ' ξ * E ξ) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => h1 x) (fun x _ => hEd x) hintE' hintθ'E hintE
  have hintcA : AEStronglyMeasurable (fun ξ : ℝ => θ ξ * E ξ) volume :=
    hintE.aestronglyMeasurable
  have hintcB : AEStronglyMeasurable (fun ξ : ℝ => θ' ξ * E ξ) volume :=
    hintθ'E.aestronglyMeasurable
  have hIBP1' : c * (∫ ξ : ℝ, θ ξ * E ξ) = -(∫ ξ : ℝ, θ' ξ * E ξ) := by
    have hpt : ∀ ξ : ℝ, θ ξ * E' ξ = c * (θ ξ * E ξ) := by
      intro ξ
      rw [hE']
      ring
    have hEq : (∫ ξ : ℝ, θ ξ * E' ξ) = c * (∫ ξ : ℝ, θ ξ * E ξ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_const_mul c (fun ξ => θ ξ * E ξ)]
    rw [← hEq, hIBP1]
  have hIBP2 : (∫ ξ : ℝ, θ' ξ * E' ξ)
      = -(∫ ξ : ℝ, θ'' ξ * E ξ) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => h2 x) (fun x _ => hEd x) hintE'θ hintθ''E hintθ'E
  have hIBP2' : c * (∫ ξ : ℝ, θ' ξ * E ξ) = -(∫ ξ : ℝ, θ'' ξ * E ξ) := by
    have hpt : ∀ ξ : ℝ, θ' ξ * E' ξ = c * (θ' ξ * E ξ) := by
      intro ξ
      rw [hE']
      ring
    have hEq : (∫ ξ : ℝ, θ' ξ * E' ξ) = c * (∫ ξ : ℝ, θ' ξ * E ξ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_const_mul c (fun ξ => θ' ξ * E ξ)]
    rw [← hEq, hIBP2]
  -- combine:  c * c * A = C
  have hcomb : c * c * (∫ ξ : ℝ, θ ξ * E ξ) = (∫ ξ : ℝ, θ'' ξ * E ξ) := by
    rw [mul_assoc, hIBP1', mul_neg, hIBP2', neg_neg]
  -- norm bookkeeping
  have hcc : c * c = ofReal (-(4 * π ^ 2 * s ^ 2)) := by
    have hI2 : I * I = -(1 : ℂ) := Complex.I_mul_I
    have h1 : c * c = (ofReal (-2 * π * s)) ^ 2 * (I * I) := by
      simp only [hc]
      ring
    rw [h1, hI2]
    push_cast
    ring
  have hccnorm : ‖c * c‖ = 4 * π ^ 2 * s ^ 2 := by
    rw [hcc, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
  have hden : (4:ℝ) * π ^ 2 * s ^ 2 ≠ 0 := by
    positivity
  have hAeq : ‖(∫ ξ : ℝ, θ ξ * E ξ)‖
      = ‖(∫ ξ : ℝ, θ'' ξ * E ξ)‖ / (4 * π ^ 2 * s ^ 2) := by
    have h1 : ‖(∫ ξ : ℝ, θ'' ξ * E ξ)‖
        = ‖c * c * (∫ ξ : ℝ, θ ξ * E ξ)‖ := by
      rw [hcomb]
    rw [h1, norm_mul, hccnorm]
    field_simp
  have hCbound : ‖(∫ ξ : ℝ, θ'' ξ * E ξ)‖ ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) := by
    refine le_trans (norm_integral_le_integral_norm
      (fun ξ => θ'' ξ * E ξ)) ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      rw [norm_mul, hEnorm ξ, mul_one])]
  have hAE : ‖∫ ξ : ℝ, θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))‖
      = ‖(∫ ξ : ℝ, θ ξ * E ξ)‖ := by
    have hpt : ∀ ξ : ℝ, θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))
        = θ ξ * E ξ := by
      intro ξ
      rw [hE]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hstep : ‖(∫ ξ : ℝ, θ'' ξ * E ξ)‖ / (4 * π ^ 2 * s ^ 2)
      ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2 * s ^ 2) :=
    (div_le_div_iff_of_pos_right (by positivity)).mpr hCbound
  calc ‖∫ ξ : ℝ, θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))‖
      _ = ‖(∫ ξ : ℝ, θ ξ * E ξ)‖ := hAE
      _ = ‖(∫ ξ : ℝ, θ'' ξ * E ξ)‖ / (4 * π ^ 2 * s ^ 2) := hAeq
      _ ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2 * s ^ 2) := hstep

end TwoIBP

section Composition

/-- **The record-1734 section-4 constant, composed.**  If `v` is the
oscillatory integral of a `C²`-integrable triple `(θ, θ', θ'')`, then the
weighted square tail of `v` beyond `X` is at most
`‖θ''‖₁² / (32 π⁴ X²)` — exactly the constant of record 1734 section 4. -/
theorem annular_v_tail_lintegral_le_of_two_ibp
    {v θ θ' θ'' : ℝ → ℂ} (hv : Measurable v)
    (hvint : ∀ s : ℝ, v s = ∫ ξ : ℝ,
      θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I)))
    (h1 : ∀ ξ : ℝ, HasDerivAt θ (θ' ξ) ξ)
    (h2 : ∀ ξ : ℝ, HasDerivAt θ' (θ'' ξ) ξ)
    (hθ1 : Integrable (fun ξ : ℝ => θ ξ) volume)
    (hθ2 : Integrable (fun ξ : ℝ => θ' ξ) volume)
    (hθ3 : Integrable (fun ξ : ℝ => θ'' ξ) volume)
    {X : ℝ} (hX : 0 < X) :
    (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2))
      ≤ ENNReal.ofReal
        ((∫ ξ : ℝ, ‖θ'' ξ‖) ^ 2 / (32 * π ^ 4 * X ^ 2)) := by
  have hintθ''pos : 0 ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) :=
    integral_nonneg fun ξ => norm_nonneg _
  have hM : (0 : ℝ) ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2) := by
    refine div_nonneg hintθ''pos ?_
    positivity
  have hvbound : ∀ s : ℝ, X ≤ s → ‖v s‖ ≤
      ((∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2)) / s ^ 2 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hX.trans_le hs
    have hne : s ≠ 0 := ne_of_gt hs0
    calc ‖v s‖ = ‖∫ ξ : ℝ,
        θ ξ * cexp ((ξ : ℂ) * (ofReal (-2 * π * s) * I))‖ := by rw [hvint s]
      _ ≤ (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2 * s ^ 2) :=
          abs_osci_integral_le_of_C2 hne h1 h2 hθ1 hθ2 hθ3
      _ = ((∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2)) / s ^ 2 := by
          field_simp
  have hvtail := lintegral_sq_moment_le_of_quadratic_decay hv (X := X)
    (M := (∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2)) hX hM hvbound
  refine le_trans hvtail ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hId : ((∫ ξ : ℝ, ‖θ'' ξ‖) / (4 * π ^ 2)) ^ 2 / (2 * X ^ 2)
      = (∫ ξ : ℝ, ‖θ'' ξ‖) ^ 2 / (32 * π ^ 4 * X ^ 2) := by
    rw [div_pow]
    ring
  exact le_of_eq hId

end Composition

end Dev
end ConnesWeilRH
