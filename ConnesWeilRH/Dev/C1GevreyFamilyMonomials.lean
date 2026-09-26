/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import Mathlib

/-!
# Gevrey window — family brick F1a: monomial algebra for the optimized-n ladder

The fixed-n rungs 1-3 write each derivative `phi_k^(n) = e^{-k/s} B_n` in closed
form, but `|supp B_n| ~ n^2 / 2.5` (record 1989), so the optimized-n family
brick must be a coefficient induction.  This module is the pure-algebra layer
of that induction (no calculus): it encodes the three differentiation moves of

    B_{n+1} = B_n' + g' * B_n,    g' = -2 k u / s^2,    s = 1 - u^2

on monomials `c * k^p * u^a * s^-b` and re-derives, as theorems, the machine
priced in record 1990 (constants 40-dps-checked there, script
`check_family_induction_1990.py`):

* `GevreyFamily.mono_invariant`: every term of level `n` satisfies
  `a ≤ n`, `p ≤ n`, `b ≤ 2n`, and `2 ≤ b` for `n ≥ 1`;
* `GevreyFamily.Afunc`: the annulus functional
  `A_n(k) = (3/5) * sum |c| k^{p+1} / k^b Gamma(b-1)`
  (the `3/5` is `1/(2u)` on `u ≥ 5/6`; `Gamma(b-1)` is the `y = k/s`
  substitution `int e^{-y} y^{b-2} dy`);
* `GevreyFamily.Afunc_step`: the three-ratio machine
  `A_{n+1} ≤ (n + 16 n^2 / k) * A_n` — per-term ratios `a ≤ n` for the
  `u`-move and `2 b (b-1) / k ≤ 8 n^2 / k` for each of the two `s`-moves
  (`Gamma(b+1) = b (b-1) Gamma(b-1)`);
* `GevreyFamily.Afunc_envelope_aux`: `A_{m+1} ≤ A_1 * prod_{j<m} (j + 16 j^2 / k)`,
  with `Afunc_one : A_1 = 6/5`;
* `GevreyFamily.sumAbs_le`: `sum |c| ≤ 5^n * n!` (the coefficient-sum bound
  feeding the two-ring middle estimate).

The conditional drops in `children` mirror the recursion: the `u`-move acts
only when `a ≥ 1` and the first `s`-move only when `b ≥ 1` (else its
coefficient `2b` vanishes); both drops keep the level-`n ≥ 1` invariants
honest, in particular `2 ≤ b`, so `Gamma(b-1)` is evaluated on `[1, oo)`.

The exact per-term identity `b - p = (n + a) / 2` of record 1990 §1(a) is
deliberately NOT formalized here: the envelope machine is ratio-based and
has no consumer for it yet (the identity prices the `k^{1-n/2}` shape, which
lives in a later sharpening brick).

No calculus is used anywhere: `phi_k`, its derivatives and the Laplace
transform enter only in later bricks (F1b identification, F2 consumer).
-/

/-- One monomial `c * k^p * u^a * s^-b` of `B_n`, `s = 1 - u^2`. -/
structure Mono where
  /-- power of `u` -/
  a : ℕ
  /-- power of `s⁻¹` -/
  b : ℕ
  /-- power of `k` -/
  p : ℕ
  /-- rational coefficient -/
  c : ℝ

namespace GevreyFamily

/-- The three differentiation moves `B ↦ B' + g' * B`, `g' = -2ku/s^2`, on one
monomial: differentiate `u^a` (only if `a ≥ 1`), differentiate `s^-b` (only if
`b ≥ 1`; coefficient `2b`), multiply by `g'` (coefficient `-2`, one extra `k`
and two extra powers of `s^-1`). -/
def children (m : Mono) : List Mono :=
  (if 0 < m.a then [{ a := m.a - 1, b := m.b, p := m.p, c := m.c * m.a }] else []) ++
    (if 0 < m.b then [{ a := m.a + 1, b := m.b + 1, p := m.p, c := m.c * (2 * m.b) }] else []) ++
    [{ a := m.a + 1, b := m.b + 2, p := m.p + 1, c := m.c * (-2 : ℝ) }]

/-- The level-`n` monomial list: `monos 0` is the seed `1` (the `B_0 = 1` of
the recursion) and `monos (n+1) = (monos n).flatMap children`. -/
def monos : ℕ → List Mono
  | 0 => [{ a := 0, b := 0, p := 0, c := 1 }]
  | n + 1 => (monos n).flatMap children

/-- Weight of a monomial in the annulus functional: `|c| * k^{p+1} / k^b *
Gamma(b-1)`.  Written as a quotient of natural powers so no `zpow` is needed;
on `k ≥ 1` the quotient is `|c| k^{p-b+1}`. -/
noncomputable def weight (k : ℝ) (m : Mono) : ℝ :=
  match m with
  | ⟨_, b, p, c⟩ => |c| * (k ^ (p + 1) / k ^ b) * Real.Gamma (b - 1)

/-- The annulus functional `A_n(k) = (3/5) * sum |c| k^{p-b+1} Gamma(b-1)`
(record 1990 §1(b)): an upper bound for the `L^1` mass of `phi_k^(n)` on
`5/6 ≤ |u| < 1` after the `y = k/s` substitution. -/
noncomputable def Afunc (n : ℕ) (k : ℝ) : ℝ :=
  (3 / 5 : ℝ) * ((monos n).map (weight k)).sum

/-- Sum-list domination helper (no `List.sum_le_sum` in the library). -/
theorem sum_map_le_sum_map {f g : Mono → ℝ} :
    ∀ l : List Mono, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [] => by simp
  | x :: l => by
      intro h
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      exact add_le_add (h x List.mem_cons_self)
        (sum_map_le_sum_map l fun y hy => h y (List.mem_cons_of_mem x hy))

/-- Sums commute with `flatMap` at the level of `List.map` + `List.sum`. -/
theorem sum_flatMap_map {α : Type*} (f : α → List Mono) (w : Mono → ℝ) :
    ∀ l : List α,
      ((l.flatMap f).map w).sum = (l.map (fun x => ((f x).map w).sum)).sum
  | [] => by simp
  | x :: l => by
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, sum_flatMap_map f w l]

/-- Sums pull out constant factors. -/
theorem sum_map_mul_left (c : ℝ) (f : Mono → ℝ) :
    ∀ l : List Mono, ((l.map (fun m => c * f m)).sum) = c * ((l.map f).sum)
  | [] => by simp
  | x :: l => by
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        sum_map_mul_left c f l]
      ring

/-- Characterization of the children (forward direction only: the inductive
invariants never construct children). -/
theorem mem_children_of {m m' : Mono} (h : m' ∈ children m) :
    (0 < m.a ∧ m' = { a := m.a - 1, b := m.b, p := m.p, c := m.c * m.a }) ∨
      (0 < m.b ∧ m' = { a := m.a + 1, b := m.b + 1, p := m.p, c := m.c * (2 * m.b) }) ∨
      m' = { a := m.a + 1, b := m.b + 2, p := m.p + 1, c := m.c * (-2 : ℝ) } := by
  by_cases h1 : 0 < m.a <;> by_cases h2 : 0 < m.b <;>
    simp only [children, h1, h2, reduceIte, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, false_or] at h
  · rcases h with (heq | heq) | heq
    · exact Or.inl ⟨h1, heq⟩
    · exact Or.inr (Or.inl ⟨h2, heq⟩)
    · exact Or.inr (Or.inr heq)
  · rcases h with heq | heq
    · exact Or.inl ⟨h1, heq⟩
    · exact Or.inr (Or.inr heq)
  · rcases h with heq | heq
    · exact Or.inr (Or.inl ⟨h2, heq⟩)
    · exact Or.inr (Or.inr heq)
  · exact Or.inr (Or.inr h)

/-- The level-`0` list is the single seed monomial. -/
theorem mem_monos_zero {m : Mono} (h : m ∈ monos 0) :
    m = { a := 0, b := 0, p := 0, c := 1 } := by
  simpa [monos] using h

/-- The only child of the seed monomial is the rung-1 term `-2 k u s^-2`
(both conditional moves are dropped at the seed). -/
theorem mem_children_seed {m : Mono}
    (h : m ∈ children { a := 0, b := 0, p := 0, c := 1 }) :
    m = { a := 1, b := 2, p := 1, c := (-2 : ℝ) } := by
  rcases mem_children_of h with (⟨ha, _⟩ | ⟨hb, _⟩ | heq)
  · exact absurd ha (by simp)
  · exact absurd hb (by simp)
  · simpa using heq

/-- One-step invariant transport along `children`: the level-`n` parent bounds
give the level-`n + 1` child bounds. -/
theorem children_invariant_step {m m' : Mono} {n : ℕ} (h : m' ∈ children m)
    (ha : m.a ≤ n) (hp : m.p ≤ n) (hb : m.b ≤ 2 * n) (h2 : 2 ≤ m.b) :
    m'.a ≤ n + 1 ∧ m'.p ≤ n + 1 ∧ m'.b ≤ 2 * (n + 1) ∧ 2 ≤ m'.b := by
  rcases mem_children_of h with (⟨_, heq⟩ | ⟨hb1, heq⟩ | heq)
  · rw [heq]
    exact ⟨show m.a - 1 ≤ n + 1 by omega, show m.p ≤ n + 1 by omega,
      show m.b ≤ 2 * (n + 1) by omega, h2⟩
  · rw [heq]
    exact ⟨show m.a + 1 ≤ n + 1 by omega, show m.p ≤ n + 1 by omega,
      show m.b + 1 ≤ 2 * (n + 1) by omega, show 2 ≤ m.b + 1 by omega⟩
  · rw [heq]
    exact ⟨show m.a + 1 ≤ n + 1 by omega, show m.p + 1 ≤ n + 1 by omega,
      show m.b + 2 ≤ 2 * (n + 1) by omega, show 2 ≤ m.b + 2 by omega⟩

/-- The invariant set of record 1990 §1(a) that the three-ratio machine needs:
`a ≤ n`, `p ≤ n`, `b ≤ 2n`, and `2 ≤ b` once `n ≥ 1`. -/
theorem mono_invariant : ∀ (n : ℕ) (m : Mono), m ∈ monos n →
    m.a ≤ n ∧ m.p ≤ n ∧ m.b ≤ 2 * n ∧ (1 ≤ n → 2 ≤ m.b) := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [mem_monos_zero hm]
    refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
    intro hcon
    simp at hcon
  | succ n ih =>
    intro m hm
    have hm2 : m ∈ (monos n).flatMap children := hm
    rw [List.mem_flatMap] at hm2
    obtain ⟨m', hm'm, hmch⟩ := hm2
    obtain ⟨h1, h2, h3, h4⟩ := ih m' hm'm
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      rw [mem_monos_zero hm'm] at hmch
      rw [mem_children_seed hmch]
      exact ⟨by simp, by simp, by simp, by simp⟩
    · obtain ⟨g1, g2, g3, g4⟩ := children_invariant_step hmch h1 h2 h3 (h4 hn1)
      exact ⟨g1, g2, g3, fun _ => g4⟩

/-- Weights are nonnegative on the terms that occur at levels `n ≥ 1`
(`b ≥ 2` puts `Gamma(b-1)` in its positive range). -/
theorem weight_nonneg (k : ℝ) (hk : 1 ≤ k) (m : Mono) (hb : 2 ≤ m.b) :
    0 ≤ weight k m := by
  have hgamma : (0 : ℝ) < (m.b : ℝ) - 1 := by
    have h2r : (2 : ℝ) ≤ (m.b : ℝ) := Nat.cast_le.mpr hb
    linarith
  refine mul_nonneg (mul_nonneg (abs_nonneg _)
    (div_nonneg (pow_nonneg (zero_le_one.trans hk) _) (pow_nonneg (zero_le_one.trans hk) _)))
    (Real.Gamma_pos_of_pos hgamma).le

/-- The `u`-differentiation move multiplies the weight by exactly `a`
(unconditionally: the weight ignores the `a`-field, so the truncated `a - 1`
is harmless and the dropped child merely contributes nothing). -/
theorem weight_move1 (k : ℝ) (m : Mono) :
    weight k { a := m.a - 1, b := m.b, p := m.p, c := m.c * m.a } = (m.a : ℝ) * weight k m := by
  simp only [weight, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m.a : ℝ))]
  ring

/-- The first `s`-differentiation move multiplies the weight by
`2 b (b-1) / k` (`Gamma(b) = (b-1) Gamma(b-1)`). -/
theorem weight_move2 (k : ℝ) (hk : 1 ≤ k) (m : Mono) (hb : 2 ≤ m.b) :
    weight k { a := m.a + 1, b := m.b + 1, p := m.p, c := m.c * (2 * m.b) }
      = (2 * m.b * (m.b - 1 : ℝ) / k) * weight k m := by
  have hk0 : k ≠ 0 := ne_of_gt (zero_lt_one.trans_le hk)
  have hb1 : ((m.b : ℝ) - 1) ≠ 0 := by
    have h2r : (2 : ℝ) ≤ (m.b : ℝ) := Nat.cast_le.mpr hb
    intro hc
    linarith
  have hgamma : Real.Gamma (((m.b + 1 : ℕ) : ℝ) - 1)
      = ((m.b : ℝ) - 1) * Real.Gamma ((m.b : ℝ) - 1) := by
    have h1 : (((m.b + 1 : ℕ) : ℝ) - 1) = (m.b : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    rw [h1]
    conv_lhs => rw [show ((m.b : ℕ) : ℝ) = (m.b : ℝ) - 1 + 1 from by ring]
    rw [Real.Gamma_add_one hb1]
  simp only [weight]
  rw [hgamma, show k ^ (m.b + 1) = k ^ m.b * k from pow_succ k m.b, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * m.b : ℝ))]
  field_simp

/-- The `g'`-multiplication move multiplies the weight by `2 b (b-1) / k`
(two `Gamma` recurrences; one extra `k` and two extra powers of `s^-1`). -/
theorem weight_move3 (k : ℝ) (hk : 1 ≤ k) (m : Mono) (hb : 2 ≤ m.b) :
    weight k { a := m.a + 1, b := m.b + 2, p := m.p + 1, c := m.c * (-2 : ℝ) }
      = (2 * m.b * (m.b - 1 : ℝ) / k) * weight k m := by
  have hk0 : k ≠ 0 := ne_of_gt (zero_lt_one.trans_le hk)
  have hb0 : ((m.b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb1 : ((m.b : ℝ) - 1) ≠ 0 := by
    have h2r : (2 : ℝ) ≤ (m.b : ℝ) := Nat.cast_le.mpr hb
    intro hc
    linarith
  have hgamma2 : Real.Gamma (((m.b + 2 : ℕ) : ℝ) - 1)
      = (m.b : ℝ) * ((m.b : ℝ) - 1) * Real.Gamma ((m.b : ℝ) - 1) := by
    have h1 : (((m.b + 2 : ℕ) : ℝ) - 1) = (m.b : ℝ) + 1 := by
      rw [Nat.cast_add]; ring
    rw [h1, Real.Gamma_add_one hb0]
    conv_lhs => rw [show ((m.b : ℕ) : ℝ) = (m.b : ℝ) - 1 + 1 from by ring]
    rw [Real.Gamma_add_one hb1]
    ring
  simp only [weight]
  rw [hgamma2, show k ^ (m.b + 2) = (k ^ m.b * k) * k from by rw [pow_succ, pow_succ],
    show k ^ (m.p + 1 + 1) = (k ^ m.p * k) * k from by rw [pow_succ, pow_succ],
    abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  field_simp
  ring

/-- Per-parent child-weight sum: the three move ratios `a` and `2b(b-1)/k`
twice, against the source weight (equalities, no slack). -/
theorem children_weight_sum_le (k : ℝ) (hk : 1 ≤ k) (m : Mono) (hb : 2 ≤ m.b) :
    ((children m).map (weight k)).sum
      ≤ (((m.a : ℕ) : ℝ) + ((4 * m.b * (m.b - 1) : ℕ) : ℝ) / k) * weight k m := by
  rcases Nat.eq_zero_or_pos m.a with ha | ha
  · have hna : ¬(0 < m.a) := by omega
    have hb0 : 0 < m.b := by omega
    simp only [children, hna, hb0, reduceIte, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [weight_move2 k hk m hb, weight_move3 k hk m hb]
    push_cast
    rw [Nat.cast_sub (show (1 : ℕ) ≤ m.b by omega), ha]
    ring_nf
    exact le_refl _
  · have hb0 : 0 < m.b := by omega
    simp only [children, ha, hb0, reduceIte, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [weight_move1 k m, weight_move2 k hk m hb, weight_move3 k hk m hb]
    push_cast
    rw [Nat.cast_sub (show (1 : ℕ) ≤ m.b by omega)]
    ring_nf
    exact le_refl _

/-- The three-ratio machine of record 1990 §1(b): `A_{n+1} ≤ (n + 16 n^2 / k) * A_n`. -/
theorem Afunc_step (n : ℕ) (hn : 1 ≤ n) (k : ℝ) (hk : 1 ≤ k) :
    Afunc (n + 1) k ≤ (((n : ℕ) : ℝ) + ((16 * n ^ 2 : ℕ) : ℝ) / k) * Afunc n k := by
  have hsum : ((monos (n + 1)).map (weight k)).sum
      = ((monos n).map (fun m => ((children m).map (weight k)).sum)).sum :=
    sum_flatMap_map children (weight k) (monos n)
  have hp : ∀ m ∈ monos n,
      ((children m).map (weight k)).sum
        ≤ (((n : ℕ) : ℝ) + ((16 * n ^ 2 : ℕ) : ℝ) / k) * weight k m := by
    intro m hm
    obtain ⟨ha, hp0, hbn, hbb⟩ := mono_invariant n m hm
    have hb : 2 ≤ m.b := hbb hn
    have hb' : m.b - 1 ≤ 2 * n := by omega
    have hbb' : m.b * (m.b - 1) ≤ 4 * n ^ 2 := by
      have h1 := Nat.mul_le_mul hbn hb'
      rwa [show (2 * n) * (2 * n) = 4 * n ^ 2 from by ring] at h1
    have hx4 : (4 * m.b * (m.b - 1) : ℕ) = 4 * (m.b * (m.b - 1)) := by ring
    have hbig : (4 * m.b * (m.b - 1) : ℕ) ≤ (16 * n ^ 2 : ℕ) := by
      rw [hx4]; omega
    calc ((children m).map (weight k)).sum
        ≤ (((m.a : ℕ) : ℝ) + ((4 * m.b * (m.b - 1) : ℕ) : ℝ) / k) * weight k m :=
          children_weight_sum_le k hk m hb
      _ ≤ (((n : ℕ) : ℝ) + ((16 * n ^ 2 : ℕ) : ℝ) / k) * weight k m := by
          refine mul_le_mul_of_nonneg_right (add_le_add (Nat.cast_le.2 ha) ?_)
            (weight_nonneg k hk m hb)
          have hbig' : ((4 * m.b * (m.b - 1) : ℕ) : ℝ) ≤ ((16 * n ^ 2 : ℕ) : ℝ) :=
            Nat.cast_le.2 hbig
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hbig' (inv_nonneg.2 (zero_le_one.trans hk))
  simp only [Afunc]
  rw [hsum]
  refine le_trans (mul_le_mul_of_nonneg_left (sum_map_le_sum_map _ hp) (by norm_num)) ?_
  exact le_of_eq (by rw [sum_map_mul_left]; ring)

/-- The product envelope: `A_{m+1} ≤ A_1 * prod_{j<m} (j + 16 j^2 / k)`. -/
theorem Afunc_envelope_aux (m : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    Afunc (m + 1) k
      ≤ Afunc 1 k * ∏ j ∈ Finset.range m,
          (((j + 1 : ℕ) : ℝ) + ((16 * (j + 1) ^ 2 : ℕ) : ℝ) / k) := by
  induction m with
  | zero =>
    simp only [Afunc, Nat.zero_add, Finset.range_zero, Finset.prod_empty, mul_one]
    exact le_refl _
  | succ m ih =>
    calc Afunc (m + 2) k
        ≤ (((m + 1 : ℕ) : ℝ) + ((16 * (m + 1) ^ 2 : ℕ) : ℝ) / k) * Afunc (m + 1) k :=
          Afunc_step (m + 1) (by omega) k hk
      _ ≤ (((m + 1 : ℕ) : ℝ) + ((16 * (m + 1) ^ 2 : ℕ) : ℝ) / k)
            * (Afunc 1 k * ∏ j ∈ Finset.range m,
                (((j + 1 : ℕ) : ℝ) + ((16 * (j + 1) ^ 2 : ℕ) : ℝ) / k)) := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
      _ = Afunc 1 k * ((((m + 1 : ℕ) : ℝ) + ((16 * (m + 1) ^ 2 : ℕ) : ℝ) / k)
            * ∏ j ∈ Finset.range m,
                (((j + 1 : ℕ) : ℝ) + ((16 * (j + 1) ^ 2 : ℕ) : ℝ) / k)) := by ring
      _ = Afunc 1 k * ∏ j ∈ Finset.range (m + 1),
                (((j + 1 : ℕ) : ℝ) + ((16 * (j + 1) ^ 2 : ℕ) : ℝ) / k) := by
          rw [Finset.prod_range_succ]; ring

/-- Per-parent absolute-coefficient sum: `a + 2b + 2` times `|c|` (the
conditionally dropped children contribute nothing). -/
theorem children_abs_sum_eq (m : Mono) :
    ((children m).map (fun x => |x.c|)).sum = ((m.a + 2 * m.b + 2 : ℕ) : ℝ) * |m.c| := by
  by_cases ha : 0 < m.a <;> by_cases h2 : 0 < m.b <;>
    simp only [children, ha, h2, reduceIte, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  · rw [abs_mul m.c (m.a : ℝ), abs_mul m.c (2 * ↑m.b),
      abs_of_nonneg (show (0 : ℝ) ≤ (m.a : ℝ) by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * ↑m.b by positivity),
      abs_mul m.c (-(2 : ℝ)), abs_neg (2 : ℝ),
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    push_cast
    ring
  · have hbz : m.b = 0 := by omega
    rw [hbz, abs_mul m.c (m.a : ℝ),
      abs_of_nonneg (show (0 : ℝ) ≤ (m.a : ℝ) by positivity),
      abs_mul m.c (-(2 : ℝ)), abs_neg (2 : ℝ),
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    push_cast
    ring
  · have ha0 : m.a = 0 := by omega
    rw [ha0, abs_mul m.c (2 * ↑m.b),
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * ↑m.b by positivity),
      abs_mul m.c (-(2 : ℝ)), abs_neg (2 : ℝ),
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    push_cast
    ring
  · have ha0 : m.a = 0 := by omega
    have hbz : m.b = 0 := by omega
    rw [ha0, hbz, abs_mul m.c (-(2 : ℝ)), abs_neg (2 : ℝ),
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    push_cast
    ring

/-- The coefficient-sum machine: `S_{n+1} ≤ (5n + 2) S_n` (pointwise
`a + 2b + 2 ≤ n + 4n + 2` from the invariants). -/
theorem sumAbs_step (n : ℕ) :
    ((monos (n + 1)).map (fun m => |m.c|)).sum
      ≤ ((5 * n + 2 : ℕ) : ℝ) * ((monos n).map (fun m => |m.c|)).sum := by
  have hsum : ((monos (n + 1)).map (fun m => |m.c|)).sum
      = ((monos n).map (fun m => ((children m).map (fun x => |x.c|)).sum)).sum :=
    sum_flatMap_map children (fun m => |m.c|) (monos n)
  have hp : ∀ m ∈ monos n,
      ((children m).map (fun x => |x.c|)).sum ≤ ((5 * n + 2 : ℕ) : ℝ) * |m.c| := by
    intro m hm
    obtain ⟨ha, hp0, hbn, hbb⟩ := mono_invariant n m hm
    rw [children_abs_sum_eq m]
    have hcast : ((m.a + 2 * m.b + 2 : ℕ) : ℝ) ≤ ((5 * n + 2 : ℕ) : ℝ) :=
      Nat.cast_le.2 (by omega)
    exact mul_le_mul_of_nonneg_right hcast (abs_nonneg _)
  rw [hsum]
  refine le_trans (sum_map_le_sum_map _ hp) ?_
  exact le_of_eq (sum_map_mul_left _ _ _)

/-- The coefficient-sum bound feeding the two-ring middle estimate:
`sum |c| ≤ 5^n * n!`. -/
theorem sumAbs_le (n : ℕ) :
    ((monos n).map (fun m => |m.c|)).sum ≤ (5 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp [monos]
  | succ n ih =>
    calc ((monos (n + 1)).map (fun m => |m.c|)).sum
        ≤ ((5 * n + 2 : ℕ) : ℝ) * ((monos n).map (fun m => |m.c|)).sum := sumAbs_step n
      _ ≤ ((5 * n + 2 : ℕ) : ℝ) * ((5 : ℝ) ^ n * (Nat.factorial n : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ (5 : ℝ) ^ (n + 1) * ((Nat.factorial (n + 1) : ℕ) : ℝ) := by
          have hcoef : ((5 * n + 2 : ℕ) : ℝ) ≤ ((5 * (n + 1) : ℕ) : ℝ) :=
            Nat.cast_le.2 (by omega)
          have hnonneg : (0 : ℝ) ≤ (5 : ℝ) ^ n * (Nat.factorial n : ℝ) := by positivity
          have heq : ((5 : ℝ) ^ (n + 1) * ((Nat.factorial (n + 1) : ℕ) : ℝ))
              = ((5 * (n + 1) : ℕ) : ℝ) * ((5 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
            rw [pow_succ, Nat.factorial_succ]; push_cast; ring
          rw [heq]
          exact mul_le_mul_of_nonneg_right hcoef hnonneg

/-- `monos 1` is the single rung-1 monomial `-2 k u s^-2` — an executable
cross-check of the recursion against the committed rung-1 formula. -/
theorem monos_one : monos 1 = [{ a := 1, b := 2, p := 1, c := (-2 : ℝ) }] := by
  simp [monos, children]

/-- The envelope base: `A_1 = 6/5`, independent of `k` (record 1990 §1(b)). -/
theorem Afunc_one (k : ℝ) (hk : 1 ≤ k) : Afunc 1 k = 6 / 5 := by
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (zero_lt_one.trans_le hk))
  have hpow : k ^ (1 + 1) = k ^ 2 := by norm_num
  have hG : Real.Gamma (((2 : ℕ) : ℝ) - 1) = 1 := by
    rw [show (((2 : ℕ) : ℝ) - 1) = 1 from by norm_num, Real.Gamma_one]
  simp only [Afunc, monos_one, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, weight, abs_neg,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num), hpow, div_self hk2, hG]
  norm_num

end GevreyFamily
