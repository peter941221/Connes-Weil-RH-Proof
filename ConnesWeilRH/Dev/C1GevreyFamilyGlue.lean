/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyFamilyIdentification

/-!
# Gevrey window — family brick F1c: shape bound and C-infinity glue

The optimized-n consumer (brick F2) needs two things beyond the F1b interior
identification `deriv^[n] (gevreyInner k) = exp (-k/s) * B_n`:

* a SHAPE bound for `B_n` on the window, feeding the boundary squeeze and
  the middle estimate of F2;
* the C-infinity GLUE: every iterate `deriv^[n] (gevreyInner k)` vanishes on
  `1 ≤ |u|` AND is differentiable there with derivative `0`, so that the
  order-n integration by parts of F2 has no boundary terms.

This module lands both (for `1 ≤ k`; the shape bound needs `k^p ≤ k^n`,
which inverts below `k = 1`):

* `GevreyFamily.abs_deriv_iterate_gevreyInner_le`:
  `|deriv^[n] (gevreyInner k) u| ≤ 5^n * n! * k^n * sinv^(2n) * exp (-k/s)`
  on `|u| < 1` (per-term triangle + the F1a invariants + `sumAbs_le`);
* `GevreyFamily.abs_deriv_iterate_le_sq`: the power trade
  `exp (-k/s) * s^(-2n) ≤ (2n+2)^(2n+2) * s^2 / k^(2n+2)` folded in, i.e.
  `|deriv^[n] (gevreyInner k) u| ≤ sqConst n k * (1-u^2)^2` — the
  exponential beats the polynomial with two spare powers of `s`;
* `GevreyFamily.deriv_iterate_gevreyInner_of_one_le_abs` and
  `GevreyFamily.hasDerivAt_iterate_gevreyInner_ext`: the glue, by one
  induction on `n` (exterior: eventually zero; boundary `|u| = 1`: the
  squeeze through `1 - (u+w)^2 ≤ 3 * |w|`, the brick-1 pattern);
* `GevreyFamily.continuous_iterate_gevreyInner`: every iterate is
  continuous (interior: F1b; exterior: the `0` HasDerivAt).

No Laplace transform and no gate sign here; RH is not claimed.
-/

namespace GevreyFamily

open Real Set Filter Topology MeasureTheory

/-- `sinv u ≥ 1` inside the window (`s ≤ 1`). -/
lemma sinv_one_le_of_abs_lt {u : ℝ} (h : |u| < 1) : 1 ≤ sinv u := by
  have hs : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [abs_lt.1 h]
  have hu1 : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  have hinv := (inv_le_inv₀ one_pos hs).mpr hu1
  calc 1 = (1 : ℝ)⁻¹ := by simp
    _ ≤ sinv u := by simp only [sinv]; exact hinv

/-- Same-base monotonicity of natural powers on `ℝ` for `1 ≤ a`. -/
theorem pow_le_pow_left_real {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (hmn : m ≤ n) :
    a ^ m ≤ a ^ n := by
  have hstep : ∀ j : ℕ, a ^ j ≤ a ^ (j + 1) := by
    intro j
    have h0 : (0 : ℝ) ≤ a ^ j := pow_nonneg (zero_le_one.trans ha) j
    have h2 := mul_le_mul_of_nonneg_left ha h0
    rw [pow_succ]
    linarith
  induction n with
  | zero =>
      have hm0 : m = 0 := Nat.le_zero.mp hmn
      subst hm0
      exact le_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (ih (Nat.le_of_lt_succ hlt)) (hstep n)
      · have heq : m = n + 1 := Nat.le_antisymm hmn hge
        rw [heq]

/-- Integer powers of `exp`, stated once to avoid signature drift. -/
lemma exp_pow_nat (x : ℝ) : ∀ n : ℕ, Real.exp x ^ n = Real.exp ((n : ℝ) * x)
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, exp_pow_nat x n, ← Real.exp_add]
      congr 1
      push_cast
      ring

lemma abs_pow_le_one_of_le {x : ℝ} (hx : |x| ≤ 1) (j : ℕ) : |x| ^ j ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have h0 : (0 : ℝ) ≤ |x| := abs_nonneg x
      have hm := mul_le_mul ih hx h0 zero_le_one
      linarith

/-- Per-term shape bound: every level-`n` monomial is dominated by
`|c| * k^n * sinv^(2n)` on the window. -/
theorem abs_Bmon_le {n : ℕ} (k u : ℝ) (hk : 1 ≤ k) (h : |u| < 1) (m : Mono)
    (hm : m ∈ monos n) :
    |Bmon k u m| ≤ |m.c| * k ^ n * sinv u ^ (2 * n) := by
  obtain ⟨ha, hp, hbn, _⟩ := mono_invariant n m hm
  have hu1 : |u| ≤ 1 := le_of_lt h
  have hpos : (0 : ℝ) < sinv u := sinv_pos_of_abs_lt h
  have hpu : |u ^ m.a| ≤ 1 := by
    rw [abs_pow]
    exact abs_pow_le_one_of_le hu1 m.a
  have hkp : k ^ m.p ≤ k ^ n := pow_le_pow_left_real hk hp
  have hsp : sinv u ^ m.b ≤ sinv u ^ (2 * n) :=
    pow_le_pow_left_real (sinv_one_le_of_abs_lt h) hbn
  have hkc : (0 : ℝ) ≤ k ^ m.p := pow_nonneg (zero_le_one.trans hk) m.p
  have hcc : (0 : ℝ) ≤ |m.c| := abs_nonneg m.c
  have hsc : (0 : ℝ) ≤ sinv u ^ m.b := pow_nonneg hpos.le m.b
  have hAC : |m.c| * k ^ m.p ≤ |m.c| * k ^ n :=
    mul_le_mul_of_nonneg_left hkp hcc
  have hBC : |u ^ m.a| * sinv u ^ m.b ≤ 1 * sinv u ^ (2 * n) :=
    mul_le_mul hpu hsp hsc zero_le_one
  calc |Bmon k u m| = |m.c * k ^ m.p * u ^ m.a * sinv u ^ m.b| := rfl
    _ = |m.c| * k ^ m.p * |u ^ m.a| * sinv u ^ m.b := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hkc,
          abs_of_nonneg hsc]
    _ = |m.c| * k ^ m.p * (|u ^ m.a| * sinv u ^ m.b) := by ring
    _ ≤ |m.c| * k ^ n * (1 * sinv u ^ (2 * n)) :=
        mul_le_mul hAC hBC (mul_nonneg (abs_nonneg _) hsc)
          (mul_nonneg hcc (pow_nonneg (zero_le_one.trans hk) n))
    _ = |m.c| * k ^ n * sinv u ^ (2 * n) := by ring

/-- Sum triangle inequality for absolute values over a mapped list. -/
theorem abs_map_sum_le (l : List Mono) (f : Mono → ℝ) :
    |(l.map f).sum| ≤ (l.map (fun m => |f m|)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact (abs_add_le (f x) ((l.map f).sum)).trans
        (add_le_add (le_refl _) ih)

/-- Sum-level shape bound for `B_n`. -/
theorem abs_Bsum_le {n : ℕ} (k u : ℝ) (hk : 1 ≤ k) (h : |u| < 1) :
    |Bsum n k u| ≤ ((monos n).map (fun m => |m.c|)).sum * k ^ n * sinv u ^ (2 * n) := by
  have h1 := abs_map_sum_le (monos n) (Bmon k u)
  have h2 : ∀ m ∈ monos n, |Bmon k u m|
      ≤ (k ^ n * sinv u ^ (2 * n)) * |m.c| := fun m hm =>
    (abs_Bmon_le k u hk h m hm).trans_eq (by ring)
  have h3 := sum_map_le_sum_map (monos n) h2
  have h4 := sum_map_mul_left (k ^ n * sinv u ^ (2 * n))
    (fun m : Mono => |m.c|) (monos n)
  calc |Bsum n k u| = |((monos n).map (Bmon k u)).sum| := rfl
    _ ≤ ((monos n).map (fun m => (k ^ n * sinv u ^ (2 * n)) * |m.c|)).sum :=
          le_trans h1 h3
    _ = k ^ n * sinv u ^ (2 * n) * ((monos n).map (fun m => |m.c|)).sum := h4
    _ = ((monos n).map (fun m => |m.c|)).sum * k ^ n * sinv u ^ (2 * n) := by
          ring

/-- The interior shape bound for the `n`-th derivative of the window. -/
theorem abs_deriv_iterate_gevreyInner_le (n : ℕ) (k u : ℝ) (hk : 1 ≤ k)
    (h : |u| < 1) :
    |deriv^[n] (gevreyInner k) u| ≤ (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
      * (k ^ n * sinv u ^ (2 * n) * Real.exp (-k / (1 - u ^ 2))) := by
  rw [deriv_iterate_gevreyInner n k u h, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_Bsum_le (n := n) k u hk h
  have h2 := sumAbs_le n
  have hC : (0 : ℝ) ≤ k ^ n * sinv u ^ (2 * n) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hk) n)
      (pow_nonneg (sinv_pos_of_abs_lt h).le (2 * n))
  have h3 : ((monos n).map (fun m => |m.c|)).sum * k ^ n * sinv u ^ (2 * n)
      ≤ (5 : ℝ) ^ n * (Nat.factorial n : ℝ) * (k ^ n * sinv u ^ (2 * n)) := by
    rw [show ((monos n).map (fun m => |m.c|)).sum * k ^ n * sinv u ^ (2 * n)
          = ((monos n).map (fun m => |m.c|)).sum * (k ^ n * sinv u ^ (2 * n))
          from by ring]
    exact mul_le_mul_of_nonneg_right h2 hC
  calc Real.exp (-k / (1 - u ^ 2)) * |Bsum n k u|
      ≤ Real.exp (-k / (1 - u ^ 2))
          * (((monos n).map (fun m => |m.c|)).sum * k ^ n * sinv u ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
    _ ≤ Real.exp (-k / (1 - u ^ 2))
          * ((5 : ℝ) ^ n * (Nat.factorial n : ℝ)
              * (k ^ n * sinv u ^ (2 * n))) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg _)
    _ = (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
          * (k ^ n * sinv u ^ (2 * n) * Real.exp (-k / (1 - u ^ 2))) := by ring

/-- The power trade: the exponential beats the `sinv^(2n)` polynomial with
two spare powers of `s = 1 - u^2`. -/
lemma exp_sinv_trade (k : ℝ) (hk : (0 : ℝ) < k) (n : ℕ) (u : ℝ) (h : |u| < 1) :
    Real.exp (-k / (1 - u ^ 2)) * sinv u ^ (2 * n)
      ≤ ((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ 2
          / k ^ (2 * n + 2) := by
  have hs : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [abs_lt.1 h]
  have h2n : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hK : (0 : ℝ) < k / ((2 * n + 2 : ℕ) : ℝ) := div_pos hk h2n
  have h1 := exp_neg_div_le_div (k / ((2 * n + 2 : ℕ) : ℝ)) hK (1 - u ^ 2) hs
  have h1' : Real.exp (-(k / ((2 * n + 2 : ℕ) : ℝ)) / (1 - u ^ 2))
      ≤ ((2 * n + 2 : ℕ) : ℝ) * (1 - u ^ 2) / k := by
    rw [show ((2 * n + 2 : ℕ) : ℝ) * (1 - u ^ 2) / k
          = (1 - u ^ 2) / (k / ((2 * n + 2 : ℕ) : ℝ)) from by
        field_simp [h2n.ne', hk.ne']]
    exact h1
  have hkey : Real.exp (-k / (1 - u ^ 2))
      = Real.exp (-(k / ((2 * n + 2 : ℕ) : ℝ)) / (1 - u ^ 2)) ^ (2 * n + 2) := by
    rw [exp_pow_nat]
    congr 1
    field_simp [h2n.ne', hk.ne', hs.ne']
  have hmono : Real.exp (-k / (1 - u ^ 2))
      ≤ (((2 * n + 2 : ℕ) : ℝ) * (1 - u ^ 2) / k) ^ (2 * n + 2) := by
    rw [hkey]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) h1' (2 * n + 2)
  have hexp : (((2 * n + 2 : ℕ) : ℝ) * (1 - u ^ 2) / k) ^ (2 * n + 2)
      = ((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ (2 * n + 2)
          / k ^ (2 * n + 2) := by
    rw [div_pow, mul_pow]
  simp only [sinv, inv_pow]
  have hinvnn : (0 : ℝ) ≤ ((1 - u ^ 2) ^ (2 * n))⁻¹ :=
    inv_nonneg.2 (pow_nonneg hs.le _)
  have hmono' := hmono
  rw [hexp] at hmono'
  calc Real.exp (-k / (1 - u ^ 2)) * ((1 - u ^ 2) ^ (2 * n))⁻¹
      ≤ (((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ (2 * n + 2)
          / k ^ (2 * n + 2)) * ((1 - u ^ 2) ^ (2 * n))⁻¹ :=
        mul_le_mul_of_nonneg_right hmono' hinvnn
    _ = ((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ 2
          / k ^ (2 * n + 2) := by
        field_simp [hs.ne', hk.ne', pow_ne_zero (2 * n) hs.ne']
        ring

/-- The squeeze constant for level `n`: `5^n * n! * (2n+2)^(2n+2) / k^(n+2)`. -/
noncomputable def sqConst (n : ℕ) (k : ℝ) : ℝ :=
  (5 : ℝ) ^ n * (Nat.factorial n : ℝ) * (((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2))
    / k ^ (n + 2)

lemma sqConst_pos (n : ℕ) (k : ℝ) (hk : (0 : ℝ) < k) : (0 : ℝ) < sqConst n k := by
  have h1 : (0 : ℝ) < (5 : ℝ) ^ n := pow_pos (by norm_num) n
  have h2 : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    have hf := Nat.factorial_pos n
    exact_mod_cast hf
  have h3 : (0 : ℝ) < (((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2)) :=
    pow_pos (Nat.cast_pos.2 (by omega)) _
  unfold sqConst
  exact div_pos (mul_pos (mul_pos h1 h2) h3) (pow_pos hk _)

/-- Interior bound in squeeze form: the `n`-th derivative is
`sqConst n k * (1-u^2)^2`, vanishing quadratically at the glue. -/
theorem abs_deriv_iterate_le_sq (n : ℕ) (k u : ℝ) (hk : 1 ≤ k)
    (h : |u| < 1) :
    |deriv^[n] (gevreyInner k) u| ≤ sqConst n k * (1 - u ^ 2) ^ 2 := by
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk
  have h4 := abs_deriv_iterate_gevreyInner_le n k u hk h
  have h5 := exp_sinv_trade k hk0 n u h
  have hkpos : (0 : ℝ) < k ^ n := pow_pos hk0 n
  have hp : k ^ (2 * n + 2) = k ^ n * k ^ (n + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hre : (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
      * (k ^ n * sinv u ^ (2 * n) * Real.exp (-k / (1 - u ^ 2)))
      = (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
          * (k ^ n * (Real.exp (-k / (1 - u ^ 2)) * sinv u ^ (2 * n))) := by
    ring
  rw [hre] at h4
  have heq1 : (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
      * (k ^ n * (Real.exp (-k / (1 - u ^ 2)) * sinv u ^ (2 * n)))
      ≤ (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
          * (k ^ n * (((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ 2
              / k ^ (2 * n + 2))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h5 hkpos.le) (by positivity)
  have hfinal : (5 : ℝ) ^ n * (Nat.factorial n : ℝ)
      * (k ^ n * (((2 * n + 2 : ℕ) : ℝ) ^ (2 * n + 2) * (1 - u ^ 2) ^ 2
          / k ^ (2 * n + 2)))
      = sqConst n k * (1 - u ^ 2) ^ 2 := by
    unfold sqConst
    rw [hp]
    field_simp [hk0.ne', pow_ne_zero n hk0.ne', pow_ne_zero (n + 2) hk0.ne']
  exact le_trans (le_trans h4 heq1) (le_of_eq hfinal)

/-- At a glue point, the window slack `1 - (u+w)^2` is at most `3 * |w|`. -/
lemma one_sub_sq_add_le (u w : ℝ) (h1 : |u| = 1) (h2 : |u + w| < 1) :
    1 - (u + w) ^ 2 ≤ 3 * |w| := by
  rcases (abs_eq (by norm_num)).mp h1 with hr | hl
  · subst hr
    obtain ⟨hwlo, hwhi⟩ := abs_lt.mp h2
    have hwn : w < 0 := by linarith
    have hwm : -2 < w := by linarith
    have hfac : 1 - (1 + w) ^ 2 = |w| * (2 + w) := by
      rw [abs_of_neg hwn]
      ring
    have hle2 : 2 + w ≤ 3 := by linarith
    rw [hfac]
    calc |w| * (2 + w) ≤ |w| * 3 := mul_le_mul_of_nonneg_left hle2 (abs_nonneg w)
      _ = 3 * |w| := by ring
  · subst hl
    obtain ⟨hwlo, hwhi⟩ := abs_lt.mp h2
    have hwp : (0 : ℝ) < w := by linarith
    have hw2 : w < 2 := by linarith
    have hfac : 1 - (-1 + w) ^ 2 = w * (2 - w) := by ring
    have hle : 2 - w ≤ 3 := by linarith
    rw [hfac, abs_of_pos hwp]
    calc w * (2 - w) ≤ w * 3 := mul_le_mul_of_nonneg_left hle hwp.le
      _ = 3 * w := by ring

/-- The glue, by induction on `n`: on `1 ≤ |u|` every iterate is `0` and
every iterate is differentiable there with derivative `0`. -/
theorem iterate_zero_hasDerivAt_ext (n : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    (∀ u : ℝ, 1 ≤ |u| → deriv^[n] (gevreyInner k) u = 0) ∧
    (∀ u : ℝ, 1 ≤ |u| → HasDerivAt (deriv^[n] (gevreyInner k)) 0 u) := by
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk
  induction n with
  | zero =>
      refine ⟨fun u hu => gevreyInner_of_one_le_abs k u hu, fun u hu => ?_⟩
      rcases lt_trichotomy (abs u) 1 with h | h | h
      · exact absurd h (not_lt.mpr hu)
      · exact gevreyInner_hasDerivAt_abs_one k hk0 u h
      · exact gevreyInner_hasDerivAt_of_one_lt_abs k u h
  | succ n ih =>
      obtain ⟨ihval, ihder⟩ := ih
      have hA : ∀ u : ℝ, 1 ≤ |u| → deriv^[n + 1] (gevreyInner k) u = 0 := by
        intro u hu
        rw [Function.iterate_succ_apply']
        exact (ihder u hu).deriv
      refine ⟨hA, fun u hu => ?_⟩
      rcases lt_trichotomy (abs u) 1 with h | h | h
      · exact absurd h (not_lt.mpr hu)
      · -- boundary glue: the squeeze
        have hf0 : deriv^[n + 1] (gevreyInner k) u = 0 := hA u (le_of_eq h.symm)
        have hCpos : (0 : ℝ) < sqConst (n + 1) k := sqConst_pos (n + 1) k hk0
        have g0 : Tendsto (fun w : ℝ => 9 * sqConst (n + 1) k * |w|)
            (𝓝 0) (𝓝 0) := by
          have hbase : Tendsto (fun w : ℝ => 9 * sqConst (n + 1) k * |w|) (𝓝 0)
              (𝓝 (9 * sqConst (n + 1) k * |(0 : ℝ)|)) :=
            (continuous_const.mul continuous_abs).continuousAt.tendsto
          rw [abs_zero, mul_zero] at hbase
          exact hbase
        have key : ∀ w : ℝ, ‖w‖⁻¹ * ‖deriv^[n + 1] (gevreyInner k) (u + w)‖
            ≤ 9 * sqConst (n + 1) k * |w| := by
          intro w
          by_cases hw : w = 0
          · subst hw
            simp [hf0]
          · have hwd : (0 : ℝ) < |w| := abs_pos.mpr hw
            by_cases hy : |u + w| < 1
            · have hb := abs_deriv_iterate_le_sq (n + 1) k (u + w) hk hy
              have hs3 := one_sub_sq_add_le u w h hy
              have hs0 : (0 : ℝ) ≤ 1 - (u + w) ^ 2 := by
                nlinarith [abs_lt.1 hy]
              have hs2 : (1 - (u + w) ^ 2) ^ 2 ≤ 9 * |w| * |w| := by
                calc (1 - (u + w) ^ 2) ^ 2 ≤ (3 * |w|) ^ 2 :=
                      pow_le_pow_left₀ hs0 hs3 2
                  _ = 9 * |w| * |w| := by ring
              have hsw : (1 - (u + w) ^ 2) ^ 2 / |w| ≤ 9 * |w| :=
                (div_le_iff₀ hwd).mpr hs2
              have hCnn : (0 : ℝ) ≤ sqConst (n + 1) k := hCpos.le
              rw [Real.norm_eq_abs, Real.norm_eq_abs, inv_mul_eq_div]
              calc |deriv^[n + 1] (gevreyInner k) (u + w)| / |w|
                  ≤ sqConst (n + 1) k
                      * ((1 - (u + w) ^ 2) ^ 2 / |w|) := by
                      rw [← mul_div_assoc, div_le_div_iff₀ hwd hwd]
                      exact mul_le_mul_of_nonneg_right hb hwd.le
                _ ≤ sqConst (n + 1) k * (9 * |w|) :=
                      mul_le_mul_of_nonneg_left hsw hCnn
                _ = 9 * sqConst (n + 1) k * |w| := by ring
            · rw [hA (u + w) (not_lt.mp hy), norm_zero, mul_zero]
              exact mul_nonneg (by positivity) (abs_nonneg w)
        have hmain : Tendsto (fun w : ℝ =>
            ‖w‖⁻¹ * ‖deriv^[n + 1] (gevreyInner k) (u + w)‖)
            (𝓝 0) (𝓝 0) :=
          squeeze_zero (fun w => mul_nonneg (inv_nonneg.2 (norm_nonneg w))
            (norm_nonneg _)) key g0
        have hsub : Tendsto (fun x' : ℝ =>
            ‖x' - u‖⁻¹ * ‖deriv^[n + 1] (gevreyInner k) x'‖)
            (𝓝 u) (𝓝 0) := by
          have hsub' : Tendsto (fun x' : ℝ => x' - u) (𝓝 u) (𝓝 0) := by
            have hten : Tendsto (fun x' : ℝ => x' - u) (𝓝 u) (𝓝 (u - u)) :=
              ((continuous_id.sub continuous_const).continuousAt (x := u)).tendsto
            rw [sub_self] at hten
            exact hten
          refine hmain.comp hsub' |>.congr' ?_
          filter_upwards with x'
          simp
        rw [hasDerivAt_iff_tendsto, hf0]
        simpa only [sub_zero, smul_zero] using hsub
      · -- exterior: eventually zero
        have hset : {v : ℝ | 1 < |v|} ∈ 𝓝 u :=
          (isOpen_lt continuous_const continuous_abs).mem_nhds h
        have heq : (deriv^[n + 1] (gevreyInner k))
            =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) :=
          Filter.eventuallyEq_of_mem hset fun v hv => hA v (le_of_lt hv)
        exact heq.hasDerivAt_iff.2 (hasDerivAt_const u 0)

/-- Every iterate of the window vanishes on `1 ≤ |u|`. -/
theorem deriv_iterate_gevreyInner_of_one_le_abs (n : ℕ) (k : ℝ)
    (hk : 1 ≤ k) (u : ℝ) (h : 1 ≤ |u|) :
    deriv^[n] (gevreyInner k) u = 0 :=
  (iterate_zero_hasDerivAt_ext n k hk).1 u h

/-- Every iterate of the window is differentiable with derivative `0` on
`1 ≤ |u|` (the C-infinity glue). -/
theorem hasDerivAt_iterate_gevreyInner_ext (n : ℕ) (k : ℝ)
    (hk : 1 ≤ k) (u : ℝ) (h : 1 ≤ |u|) :
    HasDerivAt (deriv^[n] (gevreyInner k)) 0 u :=
  (iterate_zero_hasDerivAt_ext n k hk).2 u h

/-- Every iterate of the window is continuous on all of `ℝ`. -/
theorem continuous_iterate_gevreyInner (n : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    Continuous (deriv^[n] (gevreyInner k)) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds h
    have heq : (deriv^[n] (gevreyInner k)) =ᶠ[𝓝 u]
        (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * Bsum n k v) :=
      Filter.eventuallyEq_of_mem hop fun v hv => deriv_iterate_gevreyInner n k v hv
    exact (heq.hasDerivAt_iff.2 (hasDerivAt_expBsum_step n k u h)).continuousAt
  · exact (hasDerivAt_iterate_gevreyInner_ext n k hk u (le_of_eq h.symm)).continuousAt
  · exact (hasDerivAt_iterate_gevreyInner_ext n k hk u (le_of_lt h)).continuousAt

lemma intervalIntegrable_iterate_gevreyInner (n : ℕ) (k : ℝ)
    (hk : 1 ≤ k) (a b : ℝ) :
    IntervalIntegrable (deriv^[n] (gevreyInner k)) volume a b :=
  (continuous_iterate_gevreyInner n k hk).intervalIntegrable (μ := volume) a b

end GevreyFamily
