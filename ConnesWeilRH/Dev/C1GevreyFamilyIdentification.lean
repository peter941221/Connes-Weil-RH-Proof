/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyFamilyMonomials
import ConnesWeilRH.Dev.C1GevreyWindow

/-!
# Gevrey window — family brick F1b: the HasDerivAt identification

With `s = 1 - u ^ 2` and `sinv u = s⁻¹`, the level-`n` polynomial of the
optimized-`n` ladder is the `GevreyFamily.Bsum` of the brick-`F1a` monomials,

    B_n(u) = Σ_{m ∈ monos n} m.c * k^{m.p} * u^{m.a} * (sinv u)^{m.b}.

This module proves the identification of record 1990's recursion
`B_{n+1} = B_n' + g' * B_n`, `g' = -2ku/s^2`, as a single `HasDerivAt`
statement whose derivative IS the next level:

* `GevreyFamily.hasDerivAt_expBsum_step`: on `|u| < 1`,
  `d/du [exp(-k/s) * B_n] = exp(-k/s) * B_{n+1}`;
* `GevreyFamily.deriv_iterate_gevreyInner`: the `n`-th derivative of the
  committed window `gevreyInner k` equals `exp(-k/s) * B_n` on `|u| < 1`.

All powers of `s⁻¹` are kept as positive powers of `sinv` (no divisions),
so the term algebra is `pow_succ`/`pow_two`/`ring` throughout.  The
truncated `u ^ (m.a - 1)` of `hasDerivAt_pow` matches the conditional
drops of `children` exactly (`a = 0` gives `0 * u ^ 0 = 0`), and the
`b = 0` collapse of the `s`-move is the only case split in the per-parent
bridge `children_Bmon_sum_eq`.

Numeric pre-check (record 1992, script `check_f1b_identification_1992.py`):
the identity `diff^n profile == exp(-k/s) * B_n` holds on a 144-row
`(n, k, u)` grid at worst relative error `1.3e-59` (60 dps), and the Lean
multiset `monos n` carries the same function as the committed merged-dict
recursion of record 1989.
-/

namespace GevreyFamily

open Real Set Filter Topology

/-- `s⁻¹` for `s = 1 - u ^ 2` (positive inside the window). -/
noncomputable def sinv (u : ℝ) : ℝ := (1 - u ^ 2)⁻¹

/-- One monomial of `B_n` at `u`: `c * k^p * u^a * (s⁻¹)^b`. -/
noncomputable def Bmon (k u : ℝ) (m : Mono) : ℝ :=
  m.c * k ^ m.p * u ^ m.a * sinv u ^ m.b

/-- The level-`n` polynomial: sum of the monomials of `monos n`. -/
noncomputable def Bsum (n : ℕ) (k u : ℝ) : ℝ :=
  ((monos n).map (Bmon k u)).sum

/-- Per-term derivative value: the `u`-move and the `s`-move terms. -/
noncomputable def dBmon (k u : ℝ) (m : Mono) : ℝ :=
  (m.c * k ^ m.p * (m.a * u ^ (m.a - 1))) * sinv u ^ m.b
    + (m.c * k ^ m.p * u ^ m.a) * ((2 * m.b) * u * sinv u ^ (m.b + 1))

noncomputable def dBsum (n : ℕ) (k u : ℝ) : ℝ :=
  ((monos n).map (dBmon k u)).sum

/-- The `g'` factor `-2ku/s^2` in `sinv` form. -/
noncomputable def gfun (k u : ℝ) : ℝ := -k * (2 * u * sinv u ^ 2)

lemma sinv_pos_of_abs_lt {u : ℝ} (h : |u| < 1) : 0 < sinv u := by
  have hu2 : (0:ℝ) < 1 - u ^ 2 := by nlinarith [abs_lt.1 h]
  exact inv_pos.mpr hu2

lemma hasDerivAt_sinv (u : ℝ) (h : |u| < 1) :
    HasDerivAt sinv (2 * u * sinv u ^ 2) u := by
  have hg : HasDerivAt (fun v : ℝ => (1:ℝ) - v ^ 2) (-2 * u) u := by
    have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h2 : HasDerivAt (fun v : ℝ => (1:ℝ) - v ^ 2) ((0:ℝ) - 2 * u) u :=
      HasDerivAt.sub (hasDerivAt_const u (1:ℝ)) h1
    simpa using h2
  have hu2 : (0:ℝ) < 1 - u ^ 2 := by nlinarith [abs_lt.1 h]
  have hinv := hg.inv (ne_of_gt hu2)
  refine HasDerivAt.congr_deriv hinv ?_
  simp only [sinv, inv_pow, div_eq_inv_mul]
  ring

/-- Helper: the `b`-th power of `sinv` differentiates to the `b + 1`-power
form (the `b = 0` collapse is exact: `2 * 0 = 0`). -/
lemma hasDerivAt_sinv_pow (u : ℝ) (h : |u| < 1) (b : ℕ) :
    HasDerivAt (fun v : ℝ => sinv v ^ b) ((2 * b) * u * sinv u ^ (b + 1)) u := by
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    simpa using hasDerivAt_const u (1:ℝ)
  · have hbase : HasDerivAt sinv (2 * u * sinv u ^ 2) u := hasDerivAt_sinv u h
    have hpow : HasDerivAt (fun v : ℝ => sinv v ^ b)
        (b * sinv u ^ (b - 1) * (2 * u * sinv u ^ 2)) u := hbase.pow b
    refine HasDerivAt.congr_deriv hpow ?_
    rw [show b * sinv u ^ (b - 1) * (2 * u * sinv u ^ 2)
          = (2 * b) * u * sinv u ^ (b - 1 + 2) from by rw [pow_add]; ring,
      show (b - 1) + 2 = b + 1 from by omega]

/-- Per-term derivative: the `u`-move and `s`-move terms of `children`. -/
lemma hasDerivAt_Bmon (k u : ℝ) (m : Mono) (h : |u| < 1) :
    HasDerivAt (fun v : ℝ => Bmon k v m) (dBmon k u m) u := by
  have hpow : HasDerivAt (fun v : ℝ => v ^ m.a) (m.a * u ^ (m.a - 1)) u :=
    hasDerivAt_pow m.a u
  have hspow : HasDerivAt (fun v : ℝ => sinv v ^ m.b)
      ((2 * m.b) * u * sinv u ^ (m.b + 1)) u := hasDerivAt_sinv_pow u h m.b
  exact HasDerivAt.mul (HasDerivAt.const_mul (m.c * k ^ m.p) hpow) hspow

/-- Derivative of a finite sum of monomials. -/
lemma hasDerivAt_map_sum (l : List Mono) (k u : ℝ) (h : |u| < 1) :
    HasDerivAt (fun v : ℝ => (l.map (fun m => Bmon k v m)).sum)
      ((l.map (fun m => dBmon k u m)).sum) u := by
  induction l with
  | nil => simpa using hasDerivAt_const u 0
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact HasDerivAt.add (hasDerivAt_Bmon k u x h) ih

/-- Per-parent bridge: the children values equal the two derivative terms.
The `u ^ (m.a - 1)` truncation makes the dropped `u`-move exact at
`a = 0`; the `b = 0` collapse is handled inside `simp` via the forced
literal arithmetic. -/
theorem children_Bmon_sum_eq (k u : ℝ) (m : Mono) :
    ((children m).map (Bmon k u)).sum
      = dBmon k u m + gfun k u * Bmon k u m := by
  by_cases ha : 0 < m.a <;> by_cases h2 : 0 < m.b
  · -- a > 0, b > 0: all three children, pure monomial algebra
    simp [children, ha, h2, Bmon, dBmon, gfun]
    ring
  · -- a > 0, b = 0: the s-move term must be forced to zero first
    have hbz : m.b = 0 := by omega
    simp [children, ha, Bmon, dBmon, gfun, hbz]
    ring
  · -- a = 0, b > 0: the u-move term must be forced to zero first
    have ha0 : m.a = 0 := by omega
    simp [children, h2, Bmon, dBmon, gfun, ha0]
    ring
  · -- a = 0, b = 0: only the third move survives
    have ha0 : m.a = 0 := by omega
    have hbz : m.b = 0 := by omega
    simp [children, Bmon, dBmon, gfun, ha0, hbz]
    ring

/-- Sum-level split: children values over a list equal the derivative terms
plus the `g'`-multiplication terms. -/
theorem sum_map_children_eq (c : ℝ) (k u : ℝ) :
    ∀ l : List Mono,
      (∀ m ∈ l, ((children m).map (Bmon k u)).sum = dBmon k u m + c * Bmon k u m) →
        ((l.flatMap children).map (Bmon k u)).sum
          = (l.map (fun m => dBmon k u m)).sum + c * (l.map (Bmon k u)).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    rw [List.flatMap_cons]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [hl x List.mem_cons_self]
    rw [ih fun m hm => hl m (List.mem_cons_of_mem _ hm)]
    ring

/-- The recursion as an identity of values: `B_{n+1} = B_n' + g' * B_n`. -/
theorem Bsum_step_eq (n : ℕ) (k u : ℝ) :
    Bsum (n + 1) k u = dBsum n k u + gfun k u * Bsum n k u := by
  have h1 := sum_map_children_eq (gfun k u) k u (monos n)
    (fun m _hm => children_Bmon_sum_eq k u m)
  calc Bsum (n + 1) k u
      = (((monos n).flatMap children).map (Bmon k u)).sum := by
        simp only [Bsum, monos]
    _ = ((monos n).map (fun m => dBmon k u m)).sum
          + gfun k u * ((monos n).map (Bmon k u)).sum := h1
    _ = dBsum n k u + gfun k u * Bsum n k u := rfl

/-- The identification step: on `|u| < 1` the derivative of
`exp(-k/s) * B_n` is `exp(-k/s) * B_{n+1}`. -/
theorem hasDerivAt_expBsum_step (n : ℕ) (k u : ℝ) (h : |u| < 1) :
    HasDerivAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * Bsum n k v)
      (Real.exp (-k / (1 - u ^ 2)) * Bsum (n + 1) k u) u := by
  have hs : HasDerivAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)))
      (Real.exp (-k / (1 - u ^ 2)) * gfun k u) u := by
    have hval : Real.exp (-k / (1 - u ^ 2)) * gfun k u
        = Real.exp (-k * sinv u) * (-k * (2 * u * sinv u ^ 2)) := by
      simp only [gfun, sinv, div_eq_inv_mul, mul_comm ((1 - u ^ 2)⁻¹) (-k)]
    rw [hval]
    have hev : (fun v : ℝ => Real.exp (-k / (1 - v ^ 2))) =ᶠ[𝓝 u]
        (fun v : ℝ => Real.exp (-k * sinv v)) :=
      Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_abs continuous_const).mem_nhds h)
        fun v _ => by
          simp only [sinv]
          rw [div_eq_inv_mul, mul_comm]
    have hcore : HasDerivAt (fun v : ℝ => -k * sinv v)
        (-k * (2 * u * sinv u ^ 2)) u :=
      HasDerivAt.const_mul (-k) (hasDerivAt_sinv u h)
    exact hev.hasDerivAt_iff.2 hcore.exp
  have hb : HasDerivAt (fun v : ℝ => Bsum n k v) (dBsum n k u) u :=
    hasDerivAt_map_sum (monos n) k u h
  have hmul := hs.mul hb
  refine HasDerivAt.congr_deriv hmul ?_
  rw [Bsum_step_eq n k u]
  ring

/-- Base value: `B_0 = 1`. -/
lemma Bsum_zero (k u : ℝ) : Bsum 0 k u = 1 := by
  simp [Bsum, monos, Bmon]

/-- Rung-1 cross-check: `B_1` is the `g'` factor (matches rung 1 of brick 2
and `gevreyDeriv`). -/
lemma Bsum_one (k u : ℝ) : Bsum 1 k u = gfun k u := by
  simp [Bsum, monos, children, Bmon, gfun]
  ring

/-- Main theorem: the `n`-th derivative of the committed window equals
`exp(-k/s) * B_n` inside the window. -/
theorem deriv_iterate_gevreyInner (n : ℕ) (k : ℝ) (u : ℝ) (h : |u| < 1) :
    deriv^[n] (gevreyInner k) u = Real.exp (-k / (1 - u ^ 2)) * Bsum n k u := by
  induction n generalizing u with
  | zero =>
    change gevreyInner k u = _
    rw [gevreyInner_of_abs_lt k u h]
    simp [Bsum_zero]
  | succ n ih =>
    have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds h
    have hfun : (deriv^[n] (gevreyInner k)) =ᶠ[𝓝 u]
        (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * Bsum n k v) :=
      Filter.eventuallyEq_of_mem hop fun v hv => ih v hv
    calc deriv^[n + 1] (gevreyInner k) u
        = deriv (deriv^[n] (gevreyInner k)) u := by
          rw [Function.iterate_succ_apply']
      _ = deriv (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * Bsum n k v) u :=
          hfun.deriv_eq
      _ = Real.exp (-k / (1 - u ^ 2)) * Bsum (n + 1) k u :=
          (hasDerivAt_expBsum_step n k u h).deriv

end GevreyFamily
