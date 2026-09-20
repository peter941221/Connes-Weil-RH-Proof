/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

/-!
# Weighted annular tail decay for the S3 uniform bound

Record 1734.  The paper record closes the one analytic remainder of record
1733: the first moment of the Hardy-transformed kernel is bounded by the
second derivative of the scattering symbol, which is `W^{2,1}` by the
elementary digamma series bounds on the vertical line `Re w = 1/4`.  This
leaf lands the abstract decay/assembly layer of sections 4-5 of record 1734:

1. `lintegral_sq_moment_le_of_quadratic_decay` — the `M^2 / (2 X^2)` moment
   of a quadratically decaying vector field (the `v`-tail carrying the
   integration-by-parts decay `|v(s)| ≤ M / s^2`);
2. `lintegral_sq_tail_le_of_cubic_decay` — the `C^2 / (2 X^4)` tail of a
   cubically decaying vector field (the Schwartz tail of `k_0`);
3. `annular_weighted_tail_tendsto_zero` — the assembled weighted tail bound
   tends to zero along the window edge, the vanishing uniform annular bound.

No carrier object, no root convolution, and no sign is touched here; the
instantiation layer (kernel readback, translation-tail identities) is the
named next step.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Filter Topology

section PowerIntegral

/-- Bridge for the negative real exponent `-2` (the literal exponent does not
syntactically match the `Nat.cast` pattern of `Real.rpow_natCast`). -/
private theorem real_rpow_neg_two_eq_inv (s : ℝ) (hs : 0 ≤ s) :
    s ^ (-2 : ℝ) = (s ^ 2)⁻¹ := by
  have h1 : s ^ (-2 : ℝ) = (s ^ (2 : ℝ))⁻¹ := Real.rpow_neg hs 2
  have h2 : (s ^ (2 : ℝ))⁻¹ = (s ^ 2)⁻¹ := congrArg Inv.inv (Real.rpow_natCast s 2)
  exact h1.trans h2

/-- Bridge for the negative real exponent `-3`. -/
private theorem real_rpow_neg_three_eq_inv (s : ℝ) (hs : 0 ≤ s) :
    s ^ (-3 : ℝ) = (s ^ 3)⁻¹ := by
  have h1 : s ^ (-3 : ℝ) = (s ^ (3 : ℝ))⁻¹ := Real.rpow_neg hs 3
  have h2 : (s ^ (3 : ℝ))⁻¹ = (s ^ 3)⁻¹ := congrArg Inv.inv (Real.rpow_natCast s 3)
  exact h1.trans h2

/-- The elementary power-tail integral `∫_[X, ∞) C · s⁻³ = C / (2 X²)`. -/
private theorem real_integral_Ici_const_rpow_neg_three (X C : ℝ) (hX : 0 < X) :
    (∫ s : ℝ in Set.Ici X, C * s ^ (-3 : ℝ)) = C / (2 * X ^ 2) := by
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (a := -3) (by norm_num) hX,
    show (-3 : ℝ) + 1 = -2 from by norm_num,
    real_rpow_neg_two_eq_inv X hX.le]
  field_simp

end PowerIntegral

section QuadraticDecay

/-- The `v`-tail moment: a field decaying like `M / s²` carries the weighted
square moment at most `M² / (2 X²)` on the half-line `[X, ∞)`.  This is the
form of record 1734 section 4, with `M = ‖θ''‖₁ / (4π²)` from the two
integrations by parts. -/
theorem lintegral_sq_moment_le_of_quadratic_decay
    {v : ℝ → ℂ} (hv : Measurable v) {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hbound : ∀ s : ℝ, X ≤ s → ‖v s‖ ≤ M / s ^ 2) :
    (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2))
      ≤ ENNReal.ofReal (M ^ 2 / (2 * X ^ 2)) := by
  have hint : Integrable (fun s : ℝ => M ^ 2 * s ^ (-3 : ℝ))
      (volume.restrict (Set.Ici X)) := by
    have hsub : Set.Ici X ⊆ Set.Ioi (X / 2) := Set.Ici_subset_Ioi.mpr (by linarith)
    have h1 : Integrable (fun s : ℝ => M ^ 2 * s ^ (-3 : ℝ))
        (volume.restrict (Set.Ioi (X / 2))) :=
      (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num)
        (by linarith : (0 : ℝ) < X / 2)).const_mul (M ^ 2)
    exact h1.mono_measure (Measure.restrict_mono_set volume hsub)
  have hkey : ∀ s : ℝ, X ≤ s → M ^ 2 / s ^ 3 = M ^ 2 * s ^ (-3 : ℝ) := by
    intro s hs
    have hs0 : 0 ≤ s := hX.le.trans hs
    have hsne : s ≠ 0 := ne_of_gt (hX.trans_le hs)
    rw [real_rpow_neg_three_eq_inv s hs0]
    field_simp
  have hpoint : ∀ s : ℝ, X ≤ s →
      ENNReal.ofReal (s * ‖v s‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2 * s ^ (-3 : ℝ)) := by
    intro s hs
    have hsX : 0 < s := hX.trans_le hs
    have hsne : s ≠ 0 := ne_of_gt hsX
    have hle : ‖v s‖ ^ 2 ≤ (M / s ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg (v s)) (div_nonneg hM (sq_nonneg s))).mpr
        (hbound s hs)
    have hmul : s * ‖v s‖ ^ 2 ≤ s * (M / s ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hle hsX.le
    have h2 : s * (M / s ^ 2) ^ 2 = M ^ 2 / s ^ 3 := by
      field_simp
    have h3 : s * ‖v s‖ ^ 2 ≤ M ^ 2 / s ^ 3 := hmul.trans h2.le
    rw [hkey s hs] at h3
    exact ENNReal.ofReal_le_ofReal h3
  calc (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2))
      ≤ (∫⁻ s in Set.Ici X, ENNReal.ofReal (M ^ 2 * s ^ (-3 : ℝ))) :=
        setLIntegral_mono (by measurability) hpoint
    _ = ENNReal.ofReal (∫ s : ℝ in Set.Ici X, M ^ 2 * s ^ (-3 : ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_mem measurableSet_Ici).mono fun s hs => by
            show (0 : ℝ) ≤ M ^ 2 * s ^ (-3 : ℝ)
            have hs0 : 0 ≤ s := hX.le.trans (Set.mem_Ici.mp hs)
            rw [← hkey s hs]
            exact div_nonneg (sq_nonneg M) (pow_nonneg hs0 3))).symm
    _ = ENNReal.ofReal (M ^ 2 / (2 * X ^ 2)) :=
        congrArg ENNReal.ofReal (real_integral_Ici_const_rpow_neg_three X (M ^ 2) hX)

end QuadraticDecay

section CubicDecay

/-- The Schwartz-type tail: a field decaying like `C / s³` carries the
weighted square moment at most `C² / (2 X⁴)` on `[X, ∞)` for `X ≥ 1`.  This
is the `k_0`-tail of record 1734 section 5. -/
theorem lintegral_sq_tail_le_of_cubic_decay
    {k : ℝ → ℂ} (hk : Measurable k) {X C : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hbound : ∀ s : ℝ, X ≤ s → ‖k s‖ ≤ C / s ^ 3) :
    (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖k s‖ ^ 2))
      ≤ ENNReal.ofReal (C ^ 2 / (2 * X ^ 4)) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXne : X ≠ 0 := ne_of_gt hX0
  have hint : Integrable (fun s : ℝ => (C ^ 2 / X ^ 2) * s ^ (-3 : ℝ))
      (volume.restrict (Set.Ici X)) := by
    have hsub : Set.Ici X ⊆ Set.Ioi (X / 2) := Set.Ici_subset_Ioi.mpr (by linarith)
    have h1 : Integrable (fun s : ℝ => (C ^ 2 / X ^ 2) * s ^ (-3 : ℝ))
        (volume.restrict (Set.Ioi (X / 2))) :=
      (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num)
        (by linarith : (0 : ℝ) < X / 2)).const_mul (C ^ 2 / X ^ 2)
    exact h1.mono_measure (Measure.restrict_mono_set volume hsub)
  have hkey : ∀ s : ℝ, X ≤ s →
      (C ^ 2 / X ^ 2) * s ^ (-3 : ℝ) = C ^ 2 / (X ^ 2 * s ^ 3) := by
    intro s hs
    have hs0 : 0 ≤ s := hX0.le.trans hs
    have hsne : s ≠ 0 := ne_of_gt (hX0.trans_le hs)
    rw [real_rpow_neg_three_eq_inv s hs0]
    field_simp
  have hpoint : ∀ s : ℝ, X ≤ s →
      ENNReal.ofReal (s * ‖k s‖ ^ 2)
        ≤ ENNReal.ofReal ((C ^ 2 / X ^ 2) * s ^ (-3 : ℝ)) := by
    intro s hs
    have hsX : 0 < s := hX0.trans_le hs
    have hsne : s ≠ 0 := ne_of_gt hsX
    have hle : ‖k s‖ ^ 2 ≤ (C / s ^ 3) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg (k s)) (div_nonneg hC (pow_nonneg (le_of_lt hsX) 3))).mpr
        (hbound s hs)
    have hmul : s * ‖k s‖ ^ 2 ≤ s * (C / s ^ 3) ^ 2 :=
      mul_le_mul_of_nonneg_left hle hsX.le
    have hsq : X ^ 2 ≤ s ^ 2 := by nlinarith
    have hden : X ^ 2 * s ^ 3 ≤ s ^ 5 :=
      calc X ^ 2 * s ^ 3 ≤ s ^ 2 * s ^ 3 :=
            mul_le_mul_of_nonneg_right hsq (pow_nonneg hsX.le 3)
        _ = s ^ 5 := by ring
    have h5 : s * (C / s ^ 3) ^ 2 ≤ C ^ 2 / (X ^ 2 * s ^ 3) := by
      calc s * (C / s ^ 3) ^ 2 = C ^ 2 / s ^ 5 := by field_simp
        _ ≤ C ^ 2 / (X ^ 2 * s ^ 3) :=
          div_le_div_of_nonneg_left (sq_nonneg C)
            (mul_pos (pow_pos hX0 2) (pow_pos hsX 3)) hden
    have h6 : s * ‖k s‖ ^ 2 ≤ C ^ 2 / (X ^ 2 * s ^ 3) := hmul.trans h5
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hkey s hs]
    exact h6
  calc (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖k s‖ ^ 2))
      ≤ (∫⁻ s in Set.Ici X, ENNReal.ofReal ((C ^ 2 / X ^ 2) * s ^ (-3 : ℝ))) :=
        setLIntegral_mono (by measurability) hpoint
    _ = ENNReal.ofReal (∫ s : ℝ in Set.Ici X, (C ^ 2 / X ^ 2) * s ^ (-3 : ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_mem measurableSet_Ici).mono fun s hs => by
            show (0 : ℝ) ≤ (C ^ 2 / X ^ 2) * s ^ (-3 : ℝ)
            have hs0 : 0 ≤ s := hX0.le.trans (Set.mem_Ici.mp hs)
            rw [hkey s hs]
            exact div_nonneg (sq_nonneg C)
              (mul_nonneg (pow_nonneg hX0.le 2) (pow_nonneg hs0 3)))).symm
    _ = ENNReal.ofReal ((C ^ 2 / X ^ 2) / (2 * X ^ 2)) :=
        congrArg ENNReal.ofReal
          (real_integral_Ici_const_rpow_neg_three X (C ^ 2 / X ^ 2) hX0)
    _ = ENNReal.ofReal (C ^ 2 / (2 * X ^ 4)) := by
        field_simp

end CubicDecay

section Assembly

/-- The assembled annular tail: for a window edge `X ≥ 1` the total weighted
tail of `k_0` and `v` is at most `(C² + M²) / X²`, and hence tends to zero as
the window edge `X = a + N` recedes.  This is record 1734 section 5's
`B(N) → 0` in the window edge. -/
theorem annular_weighted_tail_tendsto_zero
    {k v : ℝ → ℂ} (hk : Measurable k) (hv : Measurable v) {C M a : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hkbound : ∀ s : ℝ, 1 ≤ s → ‖k s‖ ≤ C / s ^ 3)
    (hvbound : ∀ s : ℝ, 0 < s → ‖v s‖ ≤ M / s ^ 2) :
    Tendsto (fun N : ℕ => (∫⁻ s in Set.Ici (a + (N : ℝ)),
        ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2)))) atTop (𝓝 0) := by
  have hmain : ∀ X : ℝ, 1 ≤ X →
      (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2)))
        ≤ ENNReal.ofReal ((C ^ 2 + M ^ 2) / X ^ 2) := by
    intro X hX1
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hXne : X ≠ 0 := ne_of_gt hX0
    have hmeask : Measurable (fun s : ℝ => ENNReal.ofReal (s * ‖k s‖ ^ 2)) :=
      by measurability
    have hmeasv : Measurable (fun s : ℝ => ENNReal.ofReal (s * ‖v s‖ ^ 2)) :=
      by measurability
    have hsplit : (∫⁻ s in Set.Ici X,
        ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2)))
        = (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖k s‖ ^ 2))
            + (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2)) := by
      have hae : (fun s : ℝ => ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2)))
          =ᵐ[volume.restrict (Set.Ici X)]
          (fun s : ℝ => ENNReal.ofReal (s * ‖k s‖ ^ 2)
            + ENNReal.ofReal (s * ‖v s‖ ^ 2)) := by
        filter_upwards [(ae_restrict_mem
          (measurableSet_Ici : MeasurableSet (Set.Ici X)))] with s hs
        have hs1 : 0 ≤ s := hX0.le.trans (Set.mem_Ici.mp hs)
        have hk2 : 0 ≤ ‖k s‖ ^ 2 := sq_nonneg _
        have hv2 : 0 ≤ ‖v s‖ ^ 2 := sq_nonneg _
        show ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2))
            = ENNReal.ofReal (s * ‖k s‖ ^ 2) + ENNReal.ofReal (s * ‖v s‖ ^ 2)
        rw [mul_add, ENNReal.ofReal_add (mul_nonneg hs1 hk2) (mul_nonneg hs1 hv2)]
      rw [← lintegral_add_aux hmeask hmeasv]
      exact lintegral_congr_ae hae
    have hktail := lintegral_sq_tail_le_of_cubic_decay hk (X := X) (C := C) hX1 hC
      (fun s hs => hkbound s (hX1.trans hs))
    have hvtail := lintegral_sq_moment_le_of_quadratic_decay hv (X := X) (M := M) hX0 hM
      (fun s hs => hvbound s (hX0.trans_le hs))
    have hX2 : (1 : ℝ) ≤ X ^ 2 := by
      have h3 : ((1 : ℝ) ^ 2) ≤ X ^ 2 := (sq_le_sq₀ zero_le_one hX0.le).mpr hX1
      rwa [one_pow] at h3
    have hc1 : C ^ 2 / (2 * X ^ 4) ≤ C ^ 2 / (2 * X ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg C)
        (mul_pos two_pos (pow_pos hX0 2))
        (by nlinarith [hX2, sq_nonneg X])
    have hsum : C ^ 2 / (2 * X ^ 4) + M ^ 2 / (2 * X ^ 2)
        ≤ (C ^ 2 + M ^ 2) / X ^ 2 := by
      calc C ^ 2 / (2 * X ^ 4) + M ^ 2 / (2 * X ^ 2)
          ≤ C ^ 2 / (2 * X ^ 2) + M ^ 2 / (2 * X ^ 2) := add_le_add hc1 le_rfl
        _ = (C ^ 2 + M ^ 2) / (2 * X ^ 2) := by ring
        _ ≤ (C ^ 2 + M ^ 2) / X ^ 2 :=
            div_le_div_of_nonneg_left (add_nonneg (sq_nonneg C) (sq_nonneg M))
              (pow_pos hX0 2) (by linarith [sq_nonneg X])
    calc (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * (‖k s‖ ^ 2 + ‖v s‖ ^ 2)))
        = (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖k s‖ ^ 2))
            + (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2)) := hsplit
      _ ≤ (ENNReal.ofReal (C ^ 2 / (2 * X ^ 4)))
            + (ENNReal.ofReal (M ^ 2 / (2 * X ^ 2))) := add_le_add hktail hvtail
      _ ≤ ENNReal.ofReal ((C ^ 2 + M ^ 2) / X ^ 2) := by
          rw [← ENNReal.ofReal_add
            (div_nonneg (sq_nonneg C) (mul_nonneg zero_le_two (pow_nonneg hX0.le 4)))
            (div_nonneg (sq_nonneg M) (mul_nonneg zero_le_two (pow_nonneg hX0.le 2)))]
          exact ENNReal.ofReal_le_ofReal hsum
  have hbase : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop := by
    refine (tendsto_atTop_add_const_right atTop a
      tendsto_natCast_atTop_atTop).congr' ?_
    exact Filter.Eventually.of_forall fun N => by simp [add_comm]
  have hsq : Tendsto (fun N : ℕ => (a + (N : ℝ)) ^ 2) atTop atTop :=
    tendsto_pow_atTop two_ne_zero |>.comp hbase
  have hreal : Tendsto (fun N : ℕ => (C ^ 2 + M ^ 2) / ((a + (N : ℝ)) ^ 2))
      atTop (𝓝 0) :=
    hsq.const_div_atTop (C ^ 2 + M ^ 2)
  have hreal' : Tendsto
      (fun N : ℕ => ENNReal.ofReal ((C ^ 2 + M ^ 2) / ((a + (N : ℝ)) ^ 2)))
      atTop (𝓝 (0 : ENNReal)) := by
    have key : Tendsto
        (fun N : ℕ => ENNReal.ofReal ((C ^ 2 + M ^ 2) / ((a + (N : ℝ)) ^ 2)))
        atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    rw [ENNReal.ofReal_zero] at key
    exact key
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (1 : ℝ) ≤ a + (n : ℝ) := by
    refine ⟨Nat.ceil (max (1 - a) 0) + 1, fun n hn => ?_⟩
    have h1 : (max (1 - a) 0 : ℝ) ≤ (n : ℝ) := by
      have h2 : (max (1 - a) 0 : ℝ) ≤ ((Nat.ceil (max (1 - a) 0) : ℕ) : ℝ) :=
        Nat.le_ceil _
      have h3 : ((Nat.ceil (max (1 - a) 0) : ℕ) : ℝ) ≤ (n : ℝ) := by
        have h4 : Nat.ceil (max (1 - a) 0) ≤ n := le_trans (Nat.le_succ _) hn
        exact_mod_cast h4
      exact le_trans h2 h3
    linarith [le_max_left (1 - a) 0, le_max_right (1 - a) 0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hreal'
    (Filter.Eventually.of_forall fun N => zero_le) ?_
  exact Filter.eventually_atTop.mpr ⟨N₀, fun n hn => hmain _ (hN₀ n hn)⟩

end Assembly

end Dev
end ConnesWeilRH
