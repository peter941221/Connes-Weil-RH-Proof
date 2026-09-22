/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperCore
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# C1WindowTaperLift - the smooth taper lift (N2beta component 3, tail)

The core leaf `C1WindowTaperCore` solved the corrected finite system
`T · c = y` for a taper `τ` that equals one on a sub-window.  This lift
turns the solved system into an actual owner `CompactLogTest`:

- the sphere-minimum gap lemma: the window exponential Gram quadratic is
  bounded below by `α ‖v‖²` for some `α > 0` (extreme-value theorem on the
  unit sphere plus the strict positivity branch of the quadratic);
- the sliver estimate: the `(1 - τ)`-weighted tail of the squared modulus
  is bounded by the sliver width times the uniform combination bound;
- the tapered owner `windowTaperCorrection`: `x ↦ (τ x : ℂ) · Σᵢ cᵢ e^{star(sᵢ)x}`
  for a `C^∞` compactly supported taper, with computed support, exact
  `laplaceAt` values (the corrected system realizes `y`), and the cost bound
  `compactLogL2sq f ≤ (star c ⬝ᵥ (T · c)).re`;
- the budget theorem: for `η < α` with gap `α ‖v‖² ≤ star v ⬝ᵥ (A · v)`,
  solved tapered system `T · c = y`, untapered moment-matching vector
  `A · z = y`, and sliver `∫ (1 - τ)‖U_c‖² ≤ η ‖c‖²`, one gets
  `(α - η) · compactLogL2sq f ≤ α · (star z ⬝ᵥ y).re` via the pairing
  Cauchy-Schwarz `CB² ≤ E_c · K` and the gap absorption `α P ≤ η E_c`;
- the wrapper: a `ContDiffBump` taper realizes the solve with
  `compactLogL2sq f ≤ (1 + ε) · K_loc` for every `ε > 0`, where
  `K_loc = y* G⁻¹ y` is the record-1379 Lemma E constant (record 1384
  spelling), which is exactly the N2beta deliverable of contract 009 item 3.

No numeric margin, no orbit instantiation, no N3/N4/RH claim: the nodes stay
an abstract finite family and `K_loc` stays symbolic.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 3.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowTaperLift

open MeasureTheory
open scoped Topology
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinGram
open C1WindowMellinIndependence
open C1WindowTaperCore

/-! ### Small norm helpers -/

/-- The real part of a complex number is bounded by its norm, through the
`Real.sqrt` unfolding of the complex norm. -/
theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ := by
  have h : z.re ≤ Real.sqrt (z.re * z.re + z.im * z.im) :=
    Real.le_sqrt_of_sq_le (show z.re ^ 2 ≤ z.re * z.re + z.im * z.im by
      rw [pow_two]; exact le_add_of_nonneg_right (mul_self_nonneg z.im))
  simpa using h

/-- The absolute real part is bounded by the complex norm. -/
theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ :=
  abs_le.mpr ⟨by simpa using neg_le_neg (re_le_norm (-z)), re_le_norm z⟩

/-- A point of the interval `Icc a b` has modulus at most `max |a| |b|`. -/
theorem abs_le_max_abs (a b x : ℝ) (hx : x ∈ Set.Icc a b) : |x| ≤ max |a| |b| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left _ _)
      _ ≤ a := by
        rcases le_total 0 a with ha | ha
        · rw [abs_of_nonneg ha]
          linarith
        · rw [abs_of_nonpos ha]
          linarith
      _ ≤ x := hx.1
  · calc x ≤ b := hx.2
      _ ≤ |b| := le_abs_self _
      _ ≤ max |a| |b| := le_max_right _ _

/-! ### Energy form and homogeneity of the untapered Gram quadratic -/

/-- The untapered Gram quadratic is the real window integral of the squared
modulus of the representer combination. -/
theorem windowExpGram_energy {ι : Type*} [Fintype ι] (a b : ℝ)
    (nodes : ι → ℂ) (v : ι → ℂ) :
    (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re
      = ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume := by
  classical
  show (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re
    = ∫ x : ℝ in a..b, ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2
        ∂volume
  have hz := windowExpGram_quadratic_eq_integral a b nodes v
  rw [← hz, integral_norm_sq_re]

/-- Scalar homogeneity of the representer combination. -/
theorem windowTaperComb_smul {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (r : ℝ) (v : ι → ℂ) (x : ℝ) :
    windowTaperComb nodes (r • v) x = (r : ℂ) * windowTaperComb nodes v x := by
  classical
  show (∑ i : ι, (r • v i) * Complex.exp (star (nodes i) * (x : ℂ)))
      = (r : ℂ) * ∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Algebra.smul_def]
  simp [mul_assoc]

/-- Homogeneity of the untapered Gram energy under real scalars. -/
theorem windowExpGram_energy_smul {ι : Type*} [Fintype ι] (a b : ℝ)
    (nodes : ι → ℂ) (r : ℝ) (v : ι → ℂ) :
    (dotProduct (star (r • v))
        (Matrix.mulVec (windowExpGramMatrix a b nodes) (r • v))).re
      = r * r * (dotProduct (star v)
          (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by
  classical
  rw [windowExpGram_energy, windowExpGram_energy]
  have hpoint : (fun x : ℝ => ‖windowTaperComb nodes (r • v) x‖ ^ 2)
      = fun x : ℝ => (r * r) * ‖windowTaperComb nodes v x‖ ^ 2 := by
    funext x
    have hn2 : ‖(r : ℂ)‖ ^ 2 = r * r := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]
    calc ‖windowTaperComb nodes (r • v) x‖ ^ 2
        = ‖(r : ℂ) * windowTaperComb nodes v x‖ ^ 2 := by
          rw [windowTaperComb_smul]
      _ = (‖(r : ℂ)‖ * ‖windowTaperComb nodes v x‖) ^ 2 := by rw [norm_mul]
      _ = ‖(r : ℂ)‖ ^ 2 * ‖windowTaperComb nodes v x‖ ^ 2 := by rw [mul_pow]
      _ = (r * r) * ‖windowTaperComb nodes v x‖ ^ 2 := by rw [hn2]
  have hmul : ∫ x : ℝ in a..b, (r * r) * ‖windowTaperComb nodes v x‖ ^ 2 ∂volume
      = (r * r) * ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume := by
    rw [intervalIntegral.integral_const_mul]
  rw [hpoint, hmul]

/-! ### Uniform bound and strict positivity of the energy -/

/-- The uniform bound of a representer combination: the sum of the exponent
moduli over the window's maximal modulus times the node norms. -/
noncomputable def windowTaperBound {ι : Type*} [Fintype ι]
    (a b : ℝ) (nodes : ι → ℂ) : ℝ :=
  ∑ i : ι, Real.exp (‖nodes i‖ * max |a| |b|)

/-- The representer combination is uniformly bounded on the window by
`‖coeff‖ * windowTaperBound`. -/
theorem windowTaperComb_norm_bound {ι : Type*} [Fintype ι] (a b : ℝ)
    (nodes : ι → ℂ) (coeff : ι → ℂ) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    ‖windowTaperComb nodes coeff x‖
      ≤ ‖coeff‖ * windowTaperBound a b nodes := by
  classical
  refine (norm_sum_le Finset.univ
      fun i => coeff i * Complex.exp (star (nodes i) * (x : ℂ))).trans
    ((Finset.sum_le_sum (g := fun i =>
        ‖coeff‖ * Real.exp (‖nodes i‖ * max |a| |b|)) fun i _ => ?_).trans ?_)
  · have h1 : ‖coeff i‖ ≤ ‖coeff‖ := by
      rw [Pi.norm_def]
      exact mod_cast (Finset.le_sup (f := fun b : ι => ‖coeff b‖₊)
        (Finset.mem_univ i))
    have he : ‖Complex.exp (star (nodes i) * (x : ℂ))‖
        = Real.exp ((nodes i).re * x) := by
      rw [Complex.norm_exp]
      have hre : (star (nodes i) * (x : ℂ)).re = (nodes i).re * x := by
        simp [Complex.mul_re]
      rw [hre]
    have hre : (nodes i).re * x ≤ ‖nodes i‖ * max |a| |b| := by
      calc (nodes i).re * x ≤ |(nodes i).re * x| := le_abs_self _
        _ = |(nodes i).re| * |x| := abs_mul _ _
        _ ≤ ‖nodes i‖ * max |a| |b| :=
          mul_le_mul (abs_re_le_norm _) (abs_le_max_abs a b x hx)
            (abs_nonneg _) (norm_nonneg _)
    calc ‖coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖
        = ‖coeff i‖ * ‖Complex.exp (star (nodes i) * (x : ℂ))‖ := norm_mul _ _
      _ = ‖coeff i‖ * Real.exp ((nodes i).re * x) := by rw [he]
      _ ≤ ‖coeff‖ * Real.exp (‖nodes i‖ * max |a| |b|) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr hre)
          (Real.exp_pos _).le (norm_nonneg _)
  · refine le_of_eq ?_
    show ∑ i : ι, ‖coeff‖ * Real.exp (‖nodes i‖ * max |a| |b|)
        = ‖coeff‖ * windowTaperBound a b nodes
    rw [windowTaperBound, ← Finset.mul_sum]

/-- Strict positivity of the untapered Gram energy off the origin: the
pointwise bridge and the window independence of the exponential family. -/
theorem windowExpGram_energy_strict_pos {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (hne : Function.Injective nodes)
    (v : ι → ℂ) (hv : v ≠ 0) :
    0 < (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by
  classical
  rw [windowExpGram_energy]
  by_contra hneg
  have hle : ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume ≤ 0 := by
    linarith
  have hzero : ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume = 0 :=
    le_antisymm hle
      (intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _)
  have hWc : Continuous (fun x : ℝ => ‖windowTaperComb nodes v x‖ ^ 2) := by
    show Continuous (fun x : ℝ =>
      ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2)
    continuity
  have hpt : ∀ x ∈ Set.Ioo a b, ‖windowTaperComb nodes v x‖ ^ 2 = 0 :=
    continuous_nonneg_windowIntegral_zero hab hWc hzero fun x _ => sq_nonneg _
  have hsum : ∀ x ∈ Set.Ioo a b,
      ∑ i ∈ Finset.univ, v i * Complex.exp (star (nodes i) * (x : ℂ)) = 0 := by
    intro x hx
    have h1 : ‖windowTaperComb nodes v x‖ * ‖windowTaperComb nodes v x‖ = 0 := by
      rw [← pow_two]
      exact hpt x hx
    have h2 : windowTaperComb nodes v x = 0 :=
      norm_eq_zero.mp (eq_zero_of_mul_self_eq_zero h1)
    simpa [windowTaperComb] using h2
  refine hv (funext fun i => finiteExp_windowComb_eq_zero Finset.univ hab
    (fun p => star (nodes p)) v
    (fun i hi j hj hij hpq => hij (hne (star_injective hpq)))
    hsum i (Finset.mem_univ i))

/-- The untapered Gram energy is a continuous function of the coefficients. -/
theorem windowExpGram_energy_continuous {ι : Type*} [Fintype ι] (a b : ℝ)
    (nodes : ι → ℂ) :
    Continuous fun v : ι → ℂ =>
      (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by
  classical
  have hmain : Continuous fun v : ι → ℂ =>
      ∑ i : ι, star (v i) * ∑ j : ι, windowExpGramMatrix a b nodes i j * v j := by
    continuity
  have hfold : (fun v : ι → ℂ =>
      ∑ i : ι, star (v i) * ∑ j : ι, windowExpGramMatrix a b nodes i j * v j)
      = fun v : ι → ℂ =>
          dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v) := by
    funext v
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [hfold] at hmain
  exact Complex.continuous_re.comp hmain

/-- The spectral gap of the window exponential Gram quadratic: a uniform
`α > 0` with `α ‖v‖² ≤ star v ⬝ᵥ (A · v)` for every coefficient vector.
The engine is the extreme-value theorem on the unit sphere plus homogeneity
of the quadratic under real scalars. -/
theorem windowExpGram_gap {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (hne : Function.Injective nodes) :
    ∃ α : ℝ, 0 < α ∧ ∀ v : ι → ℂ, α * ‖v‖ ^ 2
        ≤ (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by
  classical
  have hcomp : IsCompact {x : ι → ℂ | ‖x‖ = 1} := by
    have hset : Metric.sphere (0 : ι → ℂ) (1 : ℝ) = {x : ι → ℂ | ‖x‖ = 1} := by
      ext x
      rw [Metric.mem_sphere, dist_eq_norm]
      simp
    rw [← hset]
    exact isCompact_sphere (0 : ι → ℂ) 1
  obtain ⟨v₀, hv₀m, hmin⟩ :=
    hcomp.exists_isMinOn
      ⟨fun _ => 1, by
        rw [Set.mem_setOf_eq, Pi.norm_def]
        have hf : (fun b : ι => ‖(1 : ℂ)‖₊) = fun _ : ι => (1 : NNReal) := by
          funext b
          simp
        rw [hf, Finset.sup_const Finset.univ_nonempty]
        exact NNReal.coe_one⟩
      (windowExpGram_energy_continuous a b nodes).continuousOn
  have hmin' : ∀ w : ι → ℂ, ‖w‖ = 1 →
      (dotProduct (star v₀) (Matrix.mulVec (windowExpGramMatrix a b nodes) v₀)).re
        ≤ (dotProduct (star w) (Matrix.mulVec (windowExpGramMatrix a b nodes) w)).re :=
    fun w hw => hmin
      (show w ∈ {x : ι → ℂ | ‖x‖ = 1} from by rw [Set.mem_setOf_eq]; exact hw)
  set α := (dotProduct (star v₀) (Matrix.mulVec (windowExpGramMatrix a b nodes) v₀)).re
  have hα0 : 0 < α :=
    windowExpGram_energy_strict_pos hab nodes hne v₀
      (fun hz => by
        rw [hz, Set.mem_setOf_eq, norm_zero] at hv₀m
        exact absurd hv₀m.symm one_ne_zero)
  refine ⟨α, hα0, ?_⟩
  intro v
  by_cases hv0 : v = 0
  · have hE0 : (dotProduct (star (0 : ι → ℂ))
        (Matrix.mulVec (windowExpGramMatrix a b nodes) 0)).re = 0 := by
      simp
    rw [hv0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, hE0]
  · set w := (‖v‖ : ℝ)⁻¹ • v with hwdef
    have hw1 : ‖w‖ = 1 := by
      rw [hwdef, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg _)]
      field_simp [norm_ne_zero_iff.mpr hv0]
    have hvw : (‖v‖ : ℝ) • w = v := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
    have hαw : α ≤ (dotProduct (star w)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) w)).re := by
      show (dotProduct (star v₀) (Matrix.mulVec (windowExpGramMatrix a b nodes) v₀)).re
          ≤ (dotProduct (star w) (Matrix.mulVec (windowExpGramMatrix a b nodes) w)).re
      exact hmin' w hw1
    have hEv : (dotProduct (star v)
          (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re
        = ‖v‖ * ‖v‖
            * (dotProduct (star w) (Matrix.mulVec (windowExpGramMatrix a b nodes) w)).re := by
      have h := windowExpGram_energy_smul a b nodes ‖v‖ w
      rw [hvw] at h
      exact h
    rw [hEv, ← pow_two]
    nlinarith [hαw, norm_nonneg v]

/-! ### The sliver estimate -/

/-- The sliver estimate: for a continuous nonnegative taper equal to one on
the sub-window `Icc p q` of the ambient window `(a, b)`, the `(1 - τ)`-weighted
squared modulus of a representer combination is bounded by the sliver width
times the uniform combination bound squared times `‖coeff‖²`. -/
theorem windowTaperSliver_bound {ι : Type*} [Fintype ι]
    (a b p q : ℝ) (τ : ℝ → ℝ) (hτc : Continuous τ)
    (hτ0 : ∀ x, 0 ≤ τ x)
    (hτeq : ∀ x ∈ Set.Icc p q, τ x = 1)
    (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b)
    (nodes : ι → ℂ) (coeff : ι → ℂ) :
    ∫ x : ℝ in a..b, (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume
      ≤ ((b - a) - (q - p)) * (windowTaperBound a b nodes) ^ 2 * ‖coeff‖ ^ 2 := by
  classical
  set f := fun x : ℝ => (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 with hfdef
  set B := (windowTaperBound a b nodes) ^ 2 * ‖coeff‖ ^ 2 with hBdef
  have hfc : Continuous f := by
    refine Continuous.mul ?_ ?_
    · exact continuous_const.sub hτc
    · show Continuous (fun x : ℝ =>
        ‖∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2)
      continuity
  have hfiap : IntervalIntegrable f volume a p := hfc.intervalIntegrable a p
  have hfpq : IntervalIntegrable f volume p q := hfc.intervalIntegrable p q
  have hfqb : IntervalIntegrable f volume q b := hfc.intervalIntegrable q b
  have hBiap : IntervalIntegrable (fun _ : ℝ => B) volume a p :=
    (continuous_const : Continuous (fun _ : ℝ => B)).intervalIntegrable a p
  have hBiqb : IntervalIntegrable (fun _ : ℝ => B) volume q b :=
    (continuous_const : Continuous (fun _ : ℝ => B)).intervalIntegrable q b
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hle : ∀ x ∈ Set.Icc a b, f x ≤ B := by
    intro x hx
    have h1 : 1 - τ x ≤ 1 := by linarith [hτ0 x]
    have h2 : ‖windowTaperComb nodes coeff x‖ ^ 2
        ≤ (‖coeff‖ * windowTaperBound a b nodes) ^ 2 := by
      have hb := windowTaperComb_norm_bound a b nodes coeff x hx
      have h0 : 0 ≤ ‖windowTaperComb nodes coeff x‖ := norm_nonneg _
      rw [pow_two, pow_two]
      exact mul_le_mul hb hb h0 (le_trans h0 hb)
    have h3 : (‖coeff‖ * windowTaperBound a b nodes) ^ 2
        = (windowTaperBound a b nodes) ^ 2 * ‖coeff‖ ^ 2 := by ring
    show (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ≤ B
    calc (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2
        ≤ 1 * ‖windowTaperComb nodes coeff x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖windowTaperComb nodes coeff x‖ ^ 2 := one_mul _
      _ ≤ (‖coeff‖ * windowTaperBound a b nodes) ^ 2 := h2
      _ = B := by rw [h3, hBdef]
  have hmid : ∫ x : ℝ in p..q, f x ∂volume = 0 := by
    have h := intervalIntegral.integral_congr (μ := volume) (a := p) (b := q)
      (fun x hx => show f x = 0 from by
        have h1 : τ x = 1 := hτeq x (by
          rcases Set.mem_uIcc.mp hx with hmem | hmem
          · exact ⟨hmem.1, hmem.2⟩
          · exact ⟨by linarith [hpq, hmem.1, hmem.2],
              by linarith [hpq, hmem.1, hmem.2]⟩)
        show (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 = 0
        rw [h1]
        ring)
    simpa using h
  have hleft : ∫ x : ℝ in a..p, f x ≤ (p - a) * B := by
    refine (intervalIntegral.integral_mono_on hap hfiap hBiap
      (fun x hx => hle x ⟨by linarith [hx.1], by linarith [hx.2, hpq, hqb]⟩)).trans ?_
    rw [intervalIntegral.integral_const, ← smul_eq_mul]
  have hright : ∫ x : ℝ in q..b, f x ≤ (b - q) * B := by
    refine (intervalIntegral.integral_mono_on hqb hfqb hBiqb
      (fun x hx => hle x ⟨by linarith [hx.1, hap, hpq], by linarith [hx.2]⟩)).trans ?_
    rw [intervalIntegral.integral_const, ← smul_eq_mul]
  have hIaq : IntervalIntegrable f volume a q := hfc.intervalIntegrable a q
  have hsum : ∫ x : ℝ in a..b, f x ∂volume
      = (∫ x : ℝ in a..p, f x ∂volume) + (∫ x : ℝ in p..q, f x ∂volume)
        + ∫ x : ℝ in q..b, f x ∂volume := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hIaq hfqb,
      ← intervalIntegral.integral_add_adjacent_intervals hfiap hfpq]
  have hstep : (∫ x : ℝ in a..p, f x ∂volume)
      + (∫ x : ℝ in p..q, f x ∂volume) + ∫ x : ℝ in q..b, f x ∂volume
      ≤ (p - a) * B + 0 + (b - q) * B :=
    add_le_add (add_le_add hleft (le_of_eq hmid)) hright
  have key : (p - a) * B + 0 + (b - q) * B
      = ((b - a) - (q - p)) * ((windowTaperBound a b nodes) ^ 2 * ‖coeff‖ ^ 2) := by
    rw [← hBdef]
    ring
  rw [hsum]
  exact (hstep.trans (le_of_eq key)).trans (le_of_eq (by ring))

/-! ### The tapered owner: construction, values, cost -/

/-- The tapered owner: `x ↦ (τ x : ℂ) · Σᵢ cᵢ e^{star(sᵢ)x}` for a `C^∞`
compactly supported real taper, as an actual `CompactLogTest`. -/
noncomputable def windowTaperCorrection {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ) : CompactLogTest := by
  classical
  let raw : ℝ → ℂ := fun x => (τ x : ℂ) * windowTaperComb nodes coeff x
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp only [raw]
    refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp hτs) ?_
    show ContDiff ℝ ∞
      fun x : ℝ => ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))
    refine ContDiff.sum (s := Finset.univ) ?_
    intro i _
    show ContDiff ℝ ∞ fun x : ℝ => coeff i * Complex.exp (star (nodes i) * (x : ℂ))
    have hlin : ContDiff ℝ ∞ (fun x : ℝ => star (nodes i) * (x : ℂ)) :=
      (contDiff_const (𝕜 := ℝ) (c := star (nodes i))).mul Complex.ofRealCLM.contDiff
    exact (contDiff_const (𝕜 := ℝ) (c := coeff i)).mul hlin.cexp
  have hraw : raw = τ • windowTaperComb nodes coeff := by
    funext x
    exact (Algebra.smul_def (r := τ x) (x := windowTaperComb nodes coeff x)).symm
  have hcompact : HasCompactSupport raw := by
    rw [hraw]
    exact hτc.smul_right
  exact { test := hcompact.toSchwartzMap hsmooth,
          compactSupport := by simpa [raw] using hcompact }

/-- Pointwise evaluation of the tapered owner. -/
theorem windowTaperCorrection_apply {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ) (x : ℝ) :
    (windowTaperCorrection nodes coeff τ hτc hτs).test x
      = (τ x : ℂ) * windowTaperComb nodes coeff x := rfl

/-- Support inclusion of the tapered owner: supported wherever `τ` is. -/
theorem windowTaperCorrection_support {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ) {a b : ℝ}
    (hsupp : Function.support τ ⊆ Set.Ioo a b) :
    Function.support (windowTaperCorrection nodes coeff τ hτc hτs).test
      ⊆ Set.Ioo a b := by
  classical
  intro x hx
  have hne : (τ x : ℂ) * windowTaperComb nodes coeff x ≠ 0 := by
    have h1 : (windowTaperCorrection nodes coeff τ hτc hτs).test x ≠ 0 := hx
    simpa only [windowTaperCorrection_apply] using h1
  refine hsupp ?_
  intro hz
  rw [hz, Complex.ofReal_zero, zero_mul] at hne
  exact hne rfl

/-! The explicit taper owner has a zero-order seminorm bound in terms of its
coefficient vector.  This is the bridge from the Gram-selected owner to the
existing strict base-contraction consumers. -/
theorem windowTaperCorrection_seminorm_zero_zero_le
    {ι : Type*} [Fintype ι] {a b : ℝ} (hab : a < b)
    (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ)
    (hsupp : Function.support τ ⊆ Set.Ioo a b)
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1) :
    SchwartzMap.seminorm ℂ 0 0
        (windowTaperCorrection nodes coeff τ hτc hτs).test ≤
      ‖coeff‖ * windowTaperBound a b nodes := by
  have hB : 0 ≤ windowTaperBound a b nodes := by
    unfold windowTaperBound
    positivity
  apply SchwartzMap.seminorm_le_bound ℂ 0 0 _
    (mul_nonneg (norm_nonneg coeff) hB)
  intro x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
  by_cases hτx : τ x = 0
  ·
    rw [windowTaperCorrection_apply, hτx, Complex.ofReal_zero, zero_mul]
    simpa using mul_nonneg (norm_nonneg coeff) hB
  · have hxmem : x ∈ Function.support τ := by
      simpa [Function.mem_support] using hτx
    have hxIoo : x ∈ Set.Ioo a b := hsupp hxmem
    have hxIcc : x ∈ Set.Icc a b := ⟨hxIoo.1.le, hxIoo.2.le⟩
    have hτabs : |τ x| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [hτ0 x], hτ1 x⟩
    have hτnorm : ‖(τ x : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real] using hτabs
    calc
      ‖(windowTaperCorrection nodes coeff τ hτc hτs).test x‖ =
          ‖(τ x : ℂ) * windowTaperComb nodes coeff x‖ := by
            rw [windowTaperCorrection_apply]
      _ = ‖(τ x : ℂ)‖ * ‖windowTaperComb nodes coeff x‖ := norm_mul _ _
      _ ≤ 1 * (‖coeff‖ * windowTaperBound a b nodes) := by
        gcongr
        exact windowTaperComb_norm_bound a b nodes coeff x hxIcc
      _ = ‖coeff‖ * windowTaperBound a b nodes := by ring

/-- A finite matrix's entrywise norm sum bounds its action on the sup norm. -/
noncomputable def matrixEntryNormSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i : ι, ∑ j : κ, ‖A i j‖

theorem matrix_mulVec_norm_le_entryNormSum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (y : κ → ℂ) :
    ‖Matrix.mulVec A y‖ ≤ matrixEntryNormSum A * ‖y‖ := by
  classical
  have hsum_nonneg : 0 ≤ matrixEntryNormSum A := by
    unfold matrixEntryNormSum
    positivity
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg hsum_nonneg (norm_nonneg y))).mpr ?_
  intro i
  have hrow : (∑ j : κ, ‖A i j‖) ≤ matrixEntryNormSum A := by
    unfold matrixEntryNormSum
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun k : ι => ∑ j : κ, ‖A k j‖)
      (fun k _ => by positivity) (Finset.mem_univ i)
  calc
    ‖(Matrix.mulVec A y) i‖ = ‖∑ j : κ, A i j * y j‖ := by
      rfl
    _ ≤ ∑ j : κ, ‖A i j * y j‖ :=
      norm_sum_le (Finset.univ : Finset κ) (fun j => A i j * y j)
    _ = ∑ j : κ, ‖A i j‖ * ‖y j‖ := by
      simp only [norm_mul]
    _ ≤ ∑ j : κ, ‖A i j‖ * ‖y‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hyj : ‖y j‖ ≤ ‖y‖ := by
        rw [Pi.norm_def]
        exact mod_cast Finset.le_sup
          (f := fun k : κ => ‖y k‖₊) (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left hyj (norm_nonneg _)
    _ = (∑ j : κ, ‖A i j‖) * ‖y‖ := by
      rw [Finset.sum_mul]
    _ ≤ matrixEntryNormSum A * ‖y‖ :=
      mul_le_mul_of_nonneg_right hrow (norm_nonneg _)

theorem windowTaperCorrection_seminorm_zero_zero_le_inverse_entryNormSum
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℝ} (hab : a < b)
    (nodes : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ)
    (hsupp : Function.support τ ⊆ Set.Ioo a b)
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1)
    (hT : IsUnit (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes))
    (y : ι → ℂ) :
    SchwartzMap.seminorm ℂ 0 0
        (windowTaperCorrection nodes
          (Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y) τ hτc hτs).test ≤
      matrixEntryNormSum (↑hT.unit⁻¹ : Matrix ι ι ℂ) * ‖y‖ *
        windowTaperBound a b nodes := by
  have hB : 0 ≤ windowTaperBound a b nodes := by
    unfold windowTaperBound
    positivity
  have hseminorm := windowTaperCorrection_seminorm_zero_zero_le
    hab nodes (Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y) τ hτc hτs
    hsupp hτ0 hτ1
  have hcoeff := matrix_mulVec_norm_le_entryNormSum
    (↑hT.unit⁻¹ : Matrix ι ι ℂ) y
  calc
    SchwartzMap.seminorm ℂ 0 0
        (windowTaperCorrection nodes
          (Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y) τ hτc hτs).test ≤
        ‖Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y‖ *
          windowTaperBound a b nodes := hseminorm
    _ ≤ (matrixEntryNormSum (↑hT.unit⁻¹ : Matrix ι ι ℂ) * ‖y‖) *
          windowTaperBound a b nodes :=
      mul_le_mul_of_nonneg_right hcoeff hB
    _ = matrixEntryNormSum (↑hT.unit⁻¹ : Matrix ι ι ℂ) * ‖y‖ *
          windowTaperBound a b nodes := by ring

/-- The tapered owner realizes the solved system's values: `laplaceAt f sⱼ`
is the `j`-th entry of the tapered Gram applied to the coefficients. -/
theorem windowTaperCorrection_laplaceAt {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ)
    (hsupp : Function.support τ ⊆ Set.Ioo a b) (j : ι) :
    laplaceAt (windowTaperCorrection nodes coeff τ hτc hτs) (nodes j)
      = (Matrix.mulVec
          (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) coeff) j := by
  classical
  set f := windowTaperCorrection nodes coeff τ hτc hτs
  have htest : f.test = fun x : ℝ => (τ x : ℂ) * windowTaperComb nodes coeff x := rfl
  have hτcont : Continuous τ := hτs.continuous
  have hW : Continuous (windowTaperComb nodes coeff) := by
    show Continuous fun x : ℝ => ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))
    continuity
  have hper (i : ι) : Continuous (fun x : ℝ =>
      coeff i * ((τ x : ℂ) * Complex.exp ((nodes j + star (nodes i)) * (x : ℂ)))) := by
    continuity
  rw [laplaceAt_eq_windowIntegral f hab
    (windowTaperCorrection_support nodes coeff τ hτc hτs hsupp)]
  rw [htest]
  simp only []
  have hpoint : ∀ x : ℝ, Complex.exp (nodes j * (x : ℂ))
        * ((τ x : ℂ) * windowTaperComb nodes coeff x)
      = ∑ i : ι, coeff i * ((τ x : ℂ)
          * Complex.exp ((nodes j + star (nodes i)) * (x : ℂ))) := by
    intro x
    have hmerge (i : ι) : Complex.exp (nodes j * (x : ℂ))
          * Complex.exp (star (nodes i) * (x : ℂ))
        = Complex.exp ((nodes j + star (nodes i)) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc Complex.exp (nodes j * (x : ℂ))
          * ((τ x : ℂ) * ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ)))
        = ∑ i : ι, Complex.exp (nodes j * (x : ℂ))
            * ((τ x : ℂ) * (coeff i * Complex.exp (star (nodes i) * (x : ℂ)))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i : ι, coeff i
            * ((τ x : ℂ) * (Complex.exp (nodes j * (x : ℂ))
                * Complex.exp (star (nodes i) * (x : ℂ)))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ = ∑ i : ι, coeff i
            * ((τ x : ℂ) * Complex.exp ((nodes j + star (nodes i)) * (x : ℂ))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hmerge i]
  refine (intervalIntegral.integral_congr (fun x _ => hpoint x)).trans ?_
  refine ((intervalIntegral.integral_finsetSum (fun i _ =>
      (hper i).intervalIntegrable a b)).trans
    (Finset.sum_congr (g := fun i =>
        coeff i * windowTaperGram a b (fun x => (τ x : ℂ)) (nodes j) (nodes i))
      rfl fun i _ => ?_)).trans ?_
  · have hi : ∫ x : ℝ in a..b, coeff i
        * ((τ x : ℂ) * Complex.exp ((nodes j + star (nodes i)) * (x : ℂ))) ∂volume
      = coeff i * windowTaperGram a b (fun x => (τ x : ℂ)) (nodes j) (nodes i) := by
      rw [intervalIntegral.integral_const_mul, windowTaperGram]
    exact hi
  · simp only [windowTaperGramMatrix, Matrix.mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_comm]

/-- Cost bound for the tapered owner: the squared L2 norm is at most the
real tapered Gram quadratic. -/
theorem windowTaperCorrection_cost_le {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (coeff : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ)
    (hsupp : Function.support τ ⊆ Set.Ioo a b)
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1) :
    compactLogL2sq (windowTaperCorrection nodes coeff τ hτc hτs)
      ≤ (dotProduct (star coeff)
          (Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)
            coeff)).re := by
  classical
  set f := windowTaperCorrection nodes coeff τ hτc hτs
  have htest : f.test = fun x : ℝ => (τ x : ℂ) * windowTaperComb nodes coeff x := rfl
  rw [← norm_sq_windowIntegral_eq_compactLogL2sq f hab
    (windowTaperCorrection_support nodes coeff τ hτc hτs hsupp)]
  have hτcont : Continuous τ := hτs.continuous
  have hW : Continuous (windowTaperComb nodes coeff) := by
    show Continuous fun x : ℝ => ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))
    continuity
  have hfi : IntervalIntegrable (fun x : ℝ => ‖f.test x‖ ^ 2) volume a b :=
    ((f.test.smooth ⊤).continuous.norm.pow 2).intervalIntegrable a b
  have hgi : IntervalIntegrable
      (fun x : ℝ => τ x * ‖windowTaperComb nodes coeff x‖ ^ 2) volume a b :=
    (hτcont.mul (hW.norm.pow 2)).intervalIntegrable a b
  refine (intervalIntegral.integral_mono_on hab.le hfi hgi ?_).trans ?_
  · intro x hx
    have hn2 : ‖(τ x : ℂ)‖ ^ 2 = τ x * τ x := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]
    calc ‖f.test x‖ ^ 2
        = ‖(τ x : ℂ) * windowTaperComb nodes coeff x‖ ^ 2 := by
          rw [htest]
      _ = ‖(τ x : ℂ)‖ ^ 2 * ‖windowTaperComb nodes coeff x‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ = τ x * τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 := by rw [hn2]
      _ = τ x * (τ x * ‖windowTaperComb nodes coeff x‖ ^ 2) := by ring
      _ ≤ τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right (hτ1 x) (sq_nonneg _)).trans (one_mul _).le)
            (hτ0 x)
  · exact le_of_eq (windowTaperGram_quadratic_re a b τ hτcont nodes coeff).symm

/-! ### The budget theorem and the (1 + ε) wrapper -/

/-- The budget theorem: for `η < α` with gap `α ‖v‖² ≤ star v ⬝ᵥ (A · v)`,
solved tapered system `T · c = y`, untapered moment-matching vector
`A · z = y`, and sliver bound `∫ (1 - τ)‖U_c‖² ≤ η ‖c‖²`, the cost of the
tapered owner is squeezed between the two solves:
`(α - η) · compactLogL2sq f ≤ α · (star z ⬝ᵥ y).re`. -/
theorem windowTaperCorrection_budget {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ)
    (coeff y z : ι → ℂ) (τ : ℝ → ℝ)
    (hτc : HasCompactSupport τ) (hτs : ContDiff ℝ ∞ τ)
    (hsupp : Function.support τ ⊆ Set.Ioo a b)
    (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1)
    (hsolveT : Matrix.mulVec
        (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) coeff = y)
    (hsolveA : Matrix.mulVec (windowExpGramMatrix a b nodes) z = y)
    (α η : ℝ) (hα : 0 < α) (hηα : η < α)
    (hgaphyp : ∀ v : ι → ℂ, α * ‖v‖ ^ 2
        ≤ (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re)
    (hsliver : ∫ x : ℝ in a..b,
        (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume ≤ η * ‖coeff‖ ^ 2) :
    (α - η) * compactLogL2sq (windowTaperCorrection nodes coeff τ hτc hτs)
      ≤ α * (dotProduct (star z) y).re := by
  classical
  set f := windowTaperCorrection nodes coeff τ hτc hτs
  set CB := (dotProduct (star coeff) y).re with hCBdef
  set K := (dotProduct (star z) y).re with hKdef
  set Ec := (dotProduct (star coeff)
      (Matrix.mulVec (windowExpGramMatrix a b nodes) coeff)).re with hEcdef
  set P := ∫ x : ℝ in a..b,
      (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume with hPdef
  have hTC : (dotProduct (star coeff)
        (Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) coeff)).re
      = CB := by rw [hsolveT, hCBdef]
  have hτcont : Continuous τ := hτs.continuous
  have hCB0 : 0 ≤ CB := by
    rw [← hTC, windowTaperGram_quadratic_re a b τ hτcont nodes coeff]
    exact intervalIntegral.integral_nonneg hab.le fun x _ =>
      mul_nonneg (hτ0 x) (sq_nonneg _)
  have hK0 : 0 ≤ K := by
    rw [hKdef, ← hsolveA, windowExpGram_energy]
    exact intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  have hcost : compactLogL2sq f ≤ CB := by
    refine le_trans (windowTaperCorrection_cost_le hab nodes coeff τ hτc hτs
      hsupp hτ0 hτ1) ?_
    rw [hTC]
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    refine intervalIntegral.integral_nonneg hab.le (fun x _ => ?_)
    exact mul_nonneg (sub_nonneg.mpr (hτ1 x)) (sq_nonneg _)
  have hW : Continuous (windowTaperComb nodes coeff) := by
    show Continuous fun x : ℝ => ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))
    continuity
  have hg1 : IntervalIntegrable
      (fun x : ℝ => τ x * ‖windowTaperComb nodes coeff x‖ ^ 2) volume a b :=
    (hτcont.mul (hW.norm.pow 2)).intervalIntegrable a b
  have hg2 : IntervalIntegrable
      (fun x : ℝ => (1 - τ x) * ‖windowTaperComb nodes coeff x‖ ^ 2) volume a b :=
    ((continuous_const.sub hτcont).mul (hW.norm.pow 2)).intervalIntegrable a b
  have hsplit : ∫ x : ℝ in a..b, ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume
      = (∫ x : ℝ in a..b, τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume) + P := by
    refine (intervalIntegral.integral_congr (fun x _ => ?_)).trans
      (intervalIntegral.integral_add hg1 hg2)
    · ring
  have hτE : ∫ x : ℝ in a..b, τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume = CB :=
    (windowTaperGram_quadratic_re a b τ hτcont nodes coeff).symm.trans hTC
  have hEc : Ec = CB + P := by
    rw [hEcdef, windowExpGram_energy, hsplit, hτE]
  by_cases hc0 : coeff = 0
  · have hcz : CB = 0 := by
      rw [hCBdef, hc0]
      simp
    have hcn0 : 0 ≤ compactLogL2sq f := by
      unfold compactLogL2sq
      exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
    rw [hcz] at hcost
    have hce : compactLogL2sq f = 0 := le_antisymm hcost hcn0
    rw [hce]
    nlinarith [hK0, hα.le]
  · have hν : ‖coeff‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
    have hsqp : 0 < ‖coeff‖ ^ 2 := pow_pos (norm_pos_iff.mpr hc0) 2
    have hη0 : 0 ≤ η := by nlinarith [hP0, hsliver, hsqp]
    have haP : α * P ≤ η * Ec := by
      calc α * P ≤ α * (η * ‖coeff‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsliver hα.le
        _ = η * (α * ‖coeff‖ ^ 2) := by ring
        _ ≤ η * Ec := mul_le_mul_of_nonneg_left (hgaphyp coeff) hη0
    have hcb2 : CB * CB ≤ Ec * K := by
      have hpair := windowExpGram_pairing_csq a b nodes coeff z (hab := hab)
      rw [hsolveA, ← hEcdef, ← hKdef] at hpair
      rw [pow_two] at hpair
      have hsq : CB * CB
          ≤ ‖dotProduct (star coeff) y‖ * ‖dotProduct (star coeff) y‖ := by
        have h1 : (dotProduct (star coeff) y).re * (dotProduct (star coeff) y).re
            ≤ Complex.normSq (dotProduct (star coeff) y) := by
          rw [Complex.normSq_apply]
          nlinarith [sq_nonneg (dotProduct (star coeff) y).im]
        have h2 : Complex.normSq (dotProduct (star coeff) y)
            = ‖dotProduct (star coeff) y‖ * ‖dotProduct (star coeff) y‖ := by
          rw [← Complex.sq_norm, pow_two]
        rw [h2] at h1
        rw [← hCBdef] at h1
        exact h1
      nlinarith [hpair, hsq, hCB0]
    have hsubpos : 0 < α - η := by linarith
    have hEcD : (α - η) * Ec ≤ α * CB := by nlinarith [haP, hEc]
    have hmain : CB * (α - η) ≤ α * K := by
      by_contra hlt0
      have hgt : α * K < CB * (α - η) := by linarith
      have hCnz : CB ≠ 0 := by
        intro h
        rw [h] at hgt
        nlinarith [hK0, hα]
      have hCBl : 0 < CB := lt_of_le_of_ne hCB0 (Ne.symm hCnz)
      have hstep : CB * (CB * (α - η)) ≤ α * K * CB := by
        nlinarith [hcb2, hEcD, hsubpos.le, hCB0, hK0]
      have hlt : CB * (α * K) < CB * (CB * (α - η)) :=
        mul_lt_mul_of_pos_left hgt hCBl
      nlinarith [hstep, hlt]
    calc (α - η) * compactLogL2sq f ≤ (α - η) * CB :=
          mul_le_mul_of_nonneg_left hcost hsubpos.le
      _ = CB * (α - η) := mul_comm _ _
      _ ≤ α * K := hmain

/-- The N2beta deliverable of contract 009 item 3: for every `ε > 0` there
is a smooth supported owner `f` realizing the node values `y` whose squared
L2 cost is at most `(1 + ε) · K_loc`, where `K_loc = star (G⁻¹ y) ⬝ᵥ y` is
the record-1379 Lemma E constant spelled through the record-1384
invertibility of the window Gram matrix.  The construction instantiates the
solved tapered system at a `ContDiffBump` taper and absorbs the sliver
budget into the `η < α` gap squeeze.  No numeric margin and no feasibility
statement beyond `a < b`, distinct nodes, and `ε > 0`. -/
theorem exists_windowTaperCorrection_cost_le_one_plus_eps
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {a b : ℝ} (hab : a < b)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : CompactLogTest,
      Function.support f.test ⊆ Set.Ioo a b ∧
        (∀ i : ι, laplaceAt f (nodes i) = y i) ∧
        compactLogL2sq f ≤ (1 + ε)
          * (dotProduct (star (Matrix.mulVec
              ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹ y)) y).re := by
  classical
  obtain ⟨α, hα0, hgaphyp⟩ := windowExpGram_gap hab nodes hne
  let TB := windowTaperBound a b nodes
  have hTB : 0 < TB := by
    show 0 < ∑ i : ι, Real.exp (‖nodes i‖ * max |a| |b|)
    refine Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  let m := (a + b) / 2
  let hw := (b - a) / 2
  have hhw : 0 < hw := by
    show 0 < (b - a) / 2
    linarith
  let Δ := ε * α / (4 * (1 + ε) * TB ^ 2)
  have hΔ : 0 < Δ := by
    show 0 < ε * α / (4 * (1 + ε) * TB ^ 2)
    refine div_pos (mul_pos hε hα0) ?_
    nlinarith [hTB]
  let δ := min (hw / 2) Δ
  have hδ : 0 < δ := lt_min (by linarith) hΔ
  have hδΔ : δ ≤ Δ := min_le_right _ _
  have hδhw : 2 * δ ≤ hw := by
    have : δ ≤ hw / 2 := min_le_left _ _
    linarith
  let rIn := hw - δ
  let rOut := hw - δ / 2
  have hrIn : 0 < rIn := by
    show 0 < hw - δ
    linarith [hδhw, hδ]
  have hrInrOut : rIn < rOut := by
    show (b - a) / 2 - δ < (b - a) / 2 - δ / 2
    linarith [hδ]
  let β : ContDiffBump m := ⟨rIn, rOut, hrIn, hrInrOut⟩
  have hleft : a < m - rOut := by
    show a < (a + b) / 2 - ((b - a) / 2 - δ / 2)
    linarith [hδ]
  have hright : m + rOut < b := by
    show (a + b) / 2 + ((b - a) / 2 - δ / 2) < b
    linarith [hδ]
  have hball : Metric.ball m rOut ⊆ Set.Ioo a b := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    refine ⟨?_, ?_⟩
    · show a < x
      have : m - rOut < x := by linarith
      linarith [hleft]
    · show x < b
      have : x < m + rOut := by linarith
      linarith [hright]
  have habsub : m - rIn < m + rIn := by
    show (a + b) / 2 - ((b - a) / 2 - δ) < (a + b) / 2 + ((b - a) / 2 - δ)
    linarith [hrIn]
  have hsub : Set.Ioo (m - rIn) (m + rIn) ⊆ Set.Ioo a b := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have h1 : m - rOut < m - rIn := by linarith [hrInrOut]
      have h2 : m - rOut < x := by linarith [h1, hx.1]
      linarith [hleft]
    · have h1 : m + rIn < m + rOut := by linarith [hrInrOut]
      have h2 : x < m + rOut := by linarith [h1, hx.2]
      linarith [hright]
  have hβb1 : ∀ x ∈ Set.Ioo (m - rIn) (m + rIn), ⇑β x = 1 := by
    intro x hx
    refine β.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |x - m| ≤ rIn
    refine abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hβcont : Continuous ⇑β := β.continuous
  have hβ0 : ∀ x, 0 ≤ ⇑β x := β.nonneg'
  have hβ1 : ∀ x, ⇑β x ≤ 1 := fun x => β.le_one
  have hβhs : HasCompactSupport ⇑β := β.hasCompactSupport
  have hβsd : ContDiff ℝ ∞ ⇑β := β.contDiff (n := ⊤)
  have hβsupp : Function.support ⇑β ⊆ Set.Ioo a b := by
    rw [β.support_eq]
    exact hball
  set hT : IsUnit (windowTaperGramMatrix a b (fun x => (⇑β x : ℂ)) nodes) :=
    windowTaperGramMatrix_isUnit_of_injective hab ⇑β hβcont hβ0
      habsub hsub hβb1 nodes hne
  set coeff := Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y
  have hsolveT : Matrix.mulVec
      (windowTaperGramMatrix a b (fun x => (⇑β x : ℂ)) nodes) coeff = y :=
    windowTaperGram_solve_mulVec hab ⇑β hβcont hβ0 habsub hsub hβb1 nodes hne y
  set hG : IsUnit (windowExpGramMatrix a b nodes) :=
    windowExpGramMatrix_isUnit_of_injective hab nodes hne
  set z := Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y
  have hsolveA : Matrix.mulVec (windowExpGramMatrix a b nodes) z = y := by
    calc Matrix.mulVec (windowExpGramMatrix a b nodes)
            (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y)
        = Matrix.mulVec (windowExpGramMatrix a b nodes
            * (↑hG.unit⁻¹ : Matrix ι ι ℂ)) y :=
            Matrix.mulVec_mulVec y (windowExpGramMatrix a b nodes)
              (↑hG.unit⁻¹ : Matrix ι ι ℂ)
      _ = Matrix.mulVec (1 : Matrix ι ι ℂ) y := by rw [hG.mul_val_inv]
      _ = y := Matrix.one_mulVec y
  set η := ((b - a) - (m + rIn - (m - rIn))) * TB ^ 2 with hηdef
  have hsliver : ∫ x : ℝ in a..b,
      (1 - ⇑β x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume ≤ η * ‖coeff‖ ^ 2 := by
    have h1 := windowTaperSliver_bound a b (m - rIn) (m + rIn) ⇑β hβcont hβ0
      (by
        intro x hx
        refine β.one_of_mem_closedBall ?_
        rw [Metric.mem_closedBall, Real.dist_eq]
        show |x - m| ≤ rIn
        refine abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by show a ≤ (a + b) / 2 - ((b - a) / 2 - δ); linarith [hδ])
      (by show (a + b) / 2 - ((b - a) / 2 - δ) ≤ (a + b) / 2 + ((b - a) / 2 - δ); linarith [hrIn])
      (by show (a + b) / 2 + ((b - a) / 2 - δ) ≤ b; linarith [hδ])
      nodes coeff
    show ∫ x : ℝ in a..b, (1 - ⇑β x) * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume
        ≤ η * ‖coeff‖ ^ 2
    have h2 : η * ‖coeff‖ ^ 2
        = ((b - a) - (m + rIn - (m - rIn))) * TB ^ 2 * ‖coeff‖ ^ 2 := by
      rw [hηdef]
    rw [h2]
    exact h1
  have hηeq : η = 2 * δ * TB ^ 2 := by
    show ((b - a) - (m + rIn - (m - rIn))) * TB ^ 2 = 2 * δ * TB ^ 2
    show ((b - a) - (((a + b) / 2 + ((b - a) / 2 - δ))
          - ((a + b) / 2 - ((b - a) / 2 - δ)))) * TB ^ 2 = 2 * δ * TB ^ 2
    ring
  have hη2 : η ≤ ε * α / (2 * (1 + ε)) := by
    rw [hηeq]
    have : 2 * Δ * TB ^ 2 = ε * α / (2 * (1 + ε)) := by
      show 2 * (ε * α / (4 * (1 + ε) * TB ^ 2)) * TB ^ 2 = ε * α / (2 * (1 + ε))
      field_simp [hTB.ne']
      ring
    calc 2 * δ * TB ^ 2 ≤ 2 * Δ * TB ^ 2 :=
          mul_le_mul_of_nonneg_right
            (show 2 * δ ≤ 2 * Δ by linarith [hδΔ])
            (sq_nonneg TB)
      _ = ε * α / (2 * (1 + ε)) := this
  have hηα : η < α := by
    have h1 : η * (2 * (1 + ε)) ≤ ε * α := by
      calc η * (2 * (1 + ε)) ≤ (ε * α / (2 * (1 + ε))) * (2 * (1 + ε)) :=
            mul_le_mul_of_nonneg_right hη2 (by nlinarith)
        _ = ε * α := by field_simp
    nlinarith [h1, hα0, hε]
  have hfact : α ≤ (1 + ε) * (α - η) := by
    have h1 : η * (1 + ε) ≤ ε * α / 2 := by
      calc η * (1 + ε) ≤ (ε * α / (2 * (1 + ε))) * (1 + ε) :=
            mul_le_mul_of_nonneg_right hη2 (by nlinarith)
        _ = ε * α / 2 := by field_simp
    nlinarith [h1, hα0, hε]
  have hsubpos : 0 < α - η := by linarith [hηα]
  set f := windowTaperCorrection nodes coeff ⇑β hβhs hβsd
  have hcost0 : 0 ≤ compactLogL2sq f := by
    unfold compactLogL2sq
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hbudget : (α - η) * compactLogL2sq f ≤ α * (dotProduct (star z) y).re :=
    windowTaperCorrection_budget hab nodes coeff y z ⇑β hβhs hβsd hβsupp hβ0 hβ1
      hsolveT hsolveA α η hα0 hηα hgaphyp hsliver
  have hval : ∀ j : ι, laplaceAt f (nodes j) = y j := by
    intro j
    have h2 := windowTaperCorrection_laplaceAt hab nodes coeff ⇑β hβhs hβsd hβsupp j
    show laplaceAt (windowTaperCorrection nodes coeff ⇑β hβhs hβsd) (nodes j) = y j
    rw [h2]
    exact congrFun hsolveT j
  have hcostfin : compactLogL2sq f ≤ (1 + ε)
      * (dotProduct (star (Matrix.mulVec
          ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹ y)) y).re := by
    have hαcost : α * compactLogL2sq f
        ≤ (1 + ε) * α * (dotProduct (star z) y).re := by
      calc α * compactLogL2sq f ≤ (1 + ε) * (α - η) * compactLogL2sq f :=
            mul_le_mul_of_nonneg_right hfact hcost0
        _ = (1 + ε) * ((α - η) * compactLogL2sq f) := by ring
        _ ≤ (1 + ε) * (α * (dotProduct (star z) y).re) :=
            mul_le_mul_of_nonneg_left hbudget (by nlinarith)
        _ = α * ((1 + ε) * (dotProduct (star z) y).re) := by ring
        _ ≤ (1 + ε) * α * (dotProduct (star z) y).re := le_of_eq (by ring)
    by_contra hlt2
    have hgt : (1 + ε)
        * (dotProduct (star (Matrix.mulVec
            ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹ y)) y).re
        < compactLogL2sq f := by linarith
    have h7 : α * ((1 + ε) * (dotProduct (star z) y).re) < α * compactLogL2sq f :=
      mul_lt_mul_of_pos_left hgt hα0
    nlinarith [hαcost, h7]
  exact ⟨f, windowTaperCorrection_support nodes coeff ⇑β hβhs hβsd hβsupp,
    hval, hcostfin⟩

end C1WindowTaperLift
end Source
end ConnesWeilRH
