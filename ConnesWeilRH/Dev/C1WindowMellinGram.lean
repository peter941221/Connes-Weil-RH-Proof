/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1QuantitativeMellinGram

/-!
# C1WindowMellinGram - concrete windowed Mellin representers (N2beta 2c)

The abstract core of record 1382 proves the minimum-norm statement over an
arbitrary supplied complex-Hilbert representer family.  This leaf supplies the
concrete owner-side half of that family: on a support window `(a, b)` the
evaluation representer for the Laplace node `s` is the raw exponential
`x ↦ exp (star s * x)`, because the register's evaluation is

```
laplaceAt f s = ∫ x in a..b, exp (s * x) * f.test x     (f supported in (a, b))
```

with the positive-character convention `CC20YoshidaConvolution.lean:35-71`.
The concrete window Gram entry `∫ x in a..b, exp ((s + star t) * x)` matches
the abstract `Matrix.gram ℂ` entry for that representer family, and the dual
inequality below converts the abstract minimum-cost statement into a cost
lower bound for actual `CompactLogTest` interpolants.

Everything here stays on raw interval integrals plus the record-1381 window
Cauchy-Schwarz brick; the `Lp` a.e.-quotient API is deliberately not touched.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 1.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowMellinGram

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export

/-- The window Gram entry for nodes `s` and `t`: the exact integral of the
pairing exponential `exp ((s + star t) * x)` over `(a, b)`.  This is the
concrete form of the abstract `finiteMellinGram` entry for the representer
family `x ↦ exp (star s * x)`. -/
noncomputable def windowExpGram (a b : ℝ) (s t : ℂ) : ℂ :=
  ∫ x : ℝ in a..b, Complex.exp ((s + star t) * (x : ℂ)) ∂volume

/-- The concrete window Gram matrix of a finite node family. -/
noncomputable def windowExpGramMatrix {ι : Type*} (a b : ℝ) (nodes : ι → ℂ) :
    Matrix ι ι ℂ :=
  fun i j => windowExpGram a b (nodes i) (nodes j)

/-- The window Gram is Hermitian: conjugating an entry swaps the two nodes.
The window order is an explicit premise, matching the record-1381 interface
style; all owner-side consumers carry it anyway. -/
theorem star_windowExpGram (a b : ℝ) (s t : ℂ) (hab : a ≤ b) :
    star (windowExpGram a b s t) = windowExpGram a b t s := by
  unfold windowExpGram
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  -- Probe round 1 lesson: the `conj` notation elaborates to `starRingEnd`,
  -- and `rw` matching does not unfold it into the `Star.star` class field, so
  -- every `conj`-spelled Mathlib lemma is imported by term mode (`exact`,
  -- `trans`, `have`), which accepts the definitional equality.
  refine ((integral_conj (f := fun x : ℝ =>
      Complex.exp ((s + star t) * (x : ℂ)))).symm).trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  calc star (Complex.exp ((s + star t) * (x : ℂ)))
      = Complex.exp (star ((s + star t) * (x : ℂ))) := (Complex.exp_conj _).symm
    _ = Complex.exp (star (s + star t) * star (x : ℂ)) :=
          congrArg Complex.exp (star_mul' _ _)
    _ = Complex.exp ((star s + t) * (x : ℂ)) := by
          congr 1
          have hx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
          rw [star_add, star_star, hx]
    _ = Complex.exp ((t + star s) * (x : ℂ)) := congrArg Complex.exp (by ring)

/-- The Laplace evaluation of a supported test is exactly the window integral
against the evaluation character. -/
theorem laplaceAt_eq_windowIntegral (f : CompactLogTest) {a b : ℝ} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b) (s : ℂ) :
    laplaceAt f s = ∫ x : ℝ in a..b,
        Complex.exp (s * (x : ℂ)) * f.test x ∂volume := by
  unfold laplaceAt
  -- The record-1381 template: turn the window side into a whole-space
  -- indicator integral before the pointwise congruence, otherwise the two
  -- sides carry different measures and `integral_congr_ae` leaves stuck
  -- metavariables.
  rw [intervalIntegral.integral_of_le hab.le,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioc a b
  · -- Ioc is left-open right-closed: a < x ∧ x ≤ b
    rw [exponentialWeight_apply, Set.indicator_of_mem hx]
  · have hx' : x ∉ Set.Ioo a b := fun hxc => hx ⟨hxc.1, le_of_lt hxc.2⟩
    have hx0 : f.test x = 0 := by
      by_contra hnz
      exact hx' (hsupp hnz)
    rw [exponentialWeight_apply, Set.indicator_of_notMem hx, hx0]
    simp

/-- For a supported test the window integral of the squared modulus is the
global squared L2 norm accessor. -/
theorem norm_sq_windowIntegral_eq_compactLogL2sq (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) :
    ∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume = compactLogL2sq f := by
  unfold compactLogL2sq
  rw [intervalIntegral.integral_of_le hab.le,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioc a b
  · simp [hx]
  · -- Ioc is left-open right-closed: a < x ∧ x ≤ b
    have hx' : x ∉ Set.Ioo a b := fun hxc => hx ⟨hxc.1, le_of_lt hxc.2⟩
    have hx0 : f.test x = 0 := by
      by_contra hnz
      exact hx' (hsupp hnz)
    rw [Set.indicator_of_notMem hx]
    simp [hx0]

/-- Pointwise: the star-conjugate of the representer combination is the
evaluation-character combination.  This is the spelling bridge between the
dual side and the Gram side. -/
theorem star_sum_exp {ι : Type*} [Fintype ι] (nodes : ι → ℂ) (coeff : ι → ℂ)
    (x : ℝ) :
    (∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))) =
      star (∑ i : ι, star (coeff i) * Complex.exp (nodes i * (x : ℂ))) := by
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `star` through `exp` and through the real cast, imported by term mode:
  have hse (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) :=
    (Complex.exp_conj z).symm
  have hx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  rw [star_mul', star_star, hse, star_mul', hx]

/-- The concrete Gram quadratic identity: the cast of the window integral of
the squared modulus of a representer combination is exactly the plain-bilinear
Gram quadratic expression `star coeff ⬝ᵥ (G · coeff)`.  This is the
owner-side instance of `finiteMellinGram_quadratic_eq_inner` for the
exponential representer family. -/
theorem windowExpGram_quadratic_eq_integral {ι : Type*} [Fintype ι]
    (a b : ℝ) (nodes : ι → ℂ) (coeff : ι → ℂ) :
    (∫ x : ℝ in a..b,
          ‖∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2
        ∂volume : ℂ) =
      dotProduct (star coeff)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) coeff) := by
  classical
  have hpoint : ∀ x : ℝ,
      (‖∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 : ℂ)
        = ∑ i : ι, ∑ j : ι,
            star (coeff i) * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))
              * coeff j) := by
    intro x
    -- For a complex number, the cast squared modulus is `conj z * z`.
    -- The power of a cast needs the `Complex` namespace spelling: the
    -- `RCLike` version names a different defeq constant that `rw` cannot
    -- see at reducible transparency.
    have hsqz (z : ℂ) : (‖z‖ : ℂ) ^ 2 = star z * z := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      rfl
    have hconj : star (∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ)))
        = ∑ i : ι, star (coeff i) * Complex.exp (nodes i * (x : ℂ)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hse (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) :=
        (Complex.exp_conj z).symm
      have hx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
      rw [star_mul', hse, star_mul', star_star, hx]
    rw [hsqz, hconj, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hmerge : Complex.exp (nodes i * (x : ℂ))
        * Complex.exp (star (nodes j) * (x : ℂ))
        = Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc star (coeff i) * Complex.exp (nodes i * (x : ℂ))
            * (coeff j * Complex.exp (star (nodes j) * (x : ℂ)))
        = star (coeff i) * coeff j
            * (Complex.exp (nodes i * (x : ℂ))
              * Complex.exp (star (nodes j) * (x : ℂ))) := by ring
      _ = star (coeff i) * coeff j
            * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) := by rw [hmerge]
      _ = star (coeff i)
            * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * coeff j) := by ring

  -- Move the real cast under the integral, expand pointwise, then integrate
  -- the double sum with each constant pulled out: the inner integral is
  -- exactly the window Gram entry.
  simp only [windowExpGram, windowExpGramMatrix, Matrix.mulVec, dotProduct]
  refine (intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun x _ => hpoint x)).trans ?_
  refine (intervalIntegral.integral_finsetSum ?_).trans ?_
  · intro i _
    have hc : Continuous fun x : ℝ => ∑ j : ι,
        star (coeff i) * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))
          * coeff j) := by
      continuity
    exact hc.intervalIntegrable a b
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : ∀ j ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun x : ℝ => star (coeff i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * coeff j))
        volume a b := by
      intro j _
      have hc : Continuous (fun x : ℝ => star (coeff i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * coeff j)) := by
        continuity
      exact hc.intervalIntegrable a b
    -- Each intermediate equality is fully typed: a `.trans` chain of holes
    -- leaves the right-hand side of the second congruence as an unsolved
    -- metavariable that the inner per-element proof cannot see.
    have hj (j : ι) : ∫ x : ℝ in a..b, star (coeff i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * coeff j) ∂volume
        = star (coeff i)
          * ((∫ x : ℝ in a..b,
              Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) ∂volume)
            * coeff j) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    exact ((intervalIntegral.integral_finsetSum hf).trans
        (Finset.sum_congr rfl fun j _ => hj j)).trans
      (Finset.mul_sum _ _ _).symm

/-- Cast normalization: the integrand `(‖W x‖ : ℂ) ^ 2` (the ascription
elaboration of a squared-modulus cast) is the cast of the real square, so its
window integral is the cast of the real window integral. -/
theorem integral_norm_sq_cast (W : ℝ → ℂ) (a b : ℝ) :
    (∫ x : ℝ in a..b, ((‖W x‖ : ℂ) ^ 2) ∂volume)
      = ↑(∫ x : ℝ in a..b, ‖W x‖ ^ 2 ∂volume) := by
  refine (intervalIntegral.integral_congr
      (fun x _ => (Complex.ofReal_pow _ 2).symm)).trans ?_
  exact intervalIntegral.integral_ofReal (μ := volume)

/-- The cast normalization composed with taking real parts. -/
theorem integral_norm_sq_re (W : ℝ → ℂ) (a b : ℝ) :
    (∫ x : ℝ in a..b, ((‖W x‖ : ℂ) ^ 2) ∂volume).re
      = ∫ x : ℝ in a..b, ‖W x‖ ^ 2 ∂volume := by
  rw [integral_norm_sq_cast, Complex.ofReal_re]

/-- The dual bound in raw form before Gram naming: the squared modulus of a
moment contraction is bounded by the window squared-modulus integral of the
coefficient combination times the window squared modulus of the test. -/
theorem windowDual_integral_le (f : CompactLogTest) {a b : ℝ} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b) {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) :
    ‖∑ i : ι, star (coeff i) * laplaceAt f (nodes i)‖ ^ 2 ≤
      (∫ x : ℝ in a..b,
          ‖∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume)
        * ∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume := by
  classical
  -- Contraction side: the moment sum is the window integral against the
  -- evaluation-character combination `H`.
  have hcontract : ∑ i : ι, star (coeff i) * laplaceAt f (nodes i)
      = ∫ x : ℝ in a..b, (∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))) * f.test x ∂volume := by
    have hper : ∀ i : ι, star (coeff i) * laplaceAt f (nodes i)
        = ∫ x : ℝ in a..b,
            star (coeff i) * (Complex.exp (nodes i * (x : ℂ)) * f.test x) ∂volume := by
      intro i
      rw [laplaceAt_eq_windowIntegral f hab hsupp,
        ← intervalIntegral.integral_const_mul]
    calc (∑ i : ι, star (coeff i) * laplaceAt f (nodes i))
        = ∑ i : ι, ∫ x : ℝ in a..b,
            star (coeff i) * (Complex.exp (nodes i * (x : ℂ)) * f.test x) ∂volume :=
          Finset.sum_congr rfl (fun i _ => hper i)
      _ = ∫ x : ℝ in a..b, ∑ i : ι,
            star (coeff i) * (Complex.exp (nodes i * (x : ℂ)) * f.test x) ∂volume := by
          have hf : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
              (fun x : ℝ => star (coeff i)
                * (Complex.exp (nodes i * (x : ℂ)) * f.test x)) volume a b := by
            intro i _
            have hc : Continuous (fun x : ℝ => star (coeff i)
                * (Complex.exp (nodes i * (x : ℂ)) * f.test x)) := by
              continuity
            exact hc.intervalIntegrable a b
          exact (intervalIntegral.integral_finsetSum hf).symm
      _ = ∫ x : ℝ in a..b, (∑ i : ι, star (coeff i)
            * Complex.exp (nodes i * (x : ℂ))) * f.test x ∂volume := by
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          rw [Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm),
            ← Finset.sum_mul]
  -- Triangle bound, then the record-1381 real window Cauchy-Schwarz.
  have htri : ‖∫ x : ℝ in a..b, (∑ i : ι, star (coeff i)
        * Complex.exp (nodes i * (x : ℂ))) * f.test x ∂volume‖
      ≤ ∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))‖ * ‖f.test x‖ ∂volume := by
    have htriEq : ∫ x : ℝ in a..b, ‖(∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))) * f.test x‖ ∂volume
        = ∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))‖ * ‖f.test x‖ ∂volume :=
      intervalIntegral.integral_congr fun x _ => norm_mul _ _
    exact (intervalIntegral.norm_integral_le_integral_norm hab.le).trans htriEq.le
  have huC : ContinuousOn (fun x : ℝ => ‖∑ i : ι, star (coeff i)
      * Complex.exp (nodes i * (x : ℂ))‖) (Set.uIcc a b) := by
    have hc : Continuous (fun x : ℝ => ‖∑ i : ι, star (coeff i)
        * Complex.exp (nodes i * (x : ℂ))‖) := by
      continuity
    exact hc.continuousOn
  have hvC : ContinuousOn (fun x : ℝ => ‖f.test x‖) (Set.uIcc a b) :=
    (f.test.smooth ⊤).continuous.norm.continuousOn
  have hcs := intervalIntegral_cauchySchwarz hab.le huC hvC
  have hhn : 0 ≤ ∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
      * Complex.exp (nodes i * (x : ℂ))‖ * ‖f.test x‖ ∂volume :=
    intervalIntegral.integral_nonneg hab.le fun x _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorm : ∀ x : ℝ, ‖∑ i : ι, star (coeff i)
      * Complex.exp (nodes i * (x : ℂ))‖
      = ‖∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))‖ := by
    intro x
    rw [star_sum_exp]
    simp only [norm_star]
  -- Assemble: square the triangle bound and fold the two C-S factors.
  have h1 : ‖∑ i : ι, star (coeff i) * laplaceAt f (nodes i)‖ ^ 2
      ≤ (∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))‖ * ‖f.test x‖ ∂volume) ^ 2 := by
    rw [hcontract]
    have hn : 0 ≤ ‖∫ x : ℝ in a..b, (∑ i : ι, star (coeff i)
        * Complex.exp (nodes i * (x : ℂ))) * f.test x ∂volume‖ := norm_nonneg _
    nlinarith [htri, hhn, hn]
  calc ‖∑ i : ι, star (coeff i) * laplaceAt f (nodes i)‖ ^ 2
      ≤ (∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))‖ * ‖f.test x‖ ∂volume) ^ 2 := h1
    _ ≤ (∫ x : ℝ in a..b, ‖∑ i : ι, star (coeff i)
          * Complex.exp (nodes i * (x : ℂ))‖ ^ 2 ∂volume)
        * ∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume := by
        simpa only [pow_two] using hcs
    _ = (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
          * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume)
        * ∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume :=
      congrArg (· * _) (intervalIntegral.integral_congr fun x _ => by
        rw [hnorm x])

/-- Main dual inequality on the owner: for every coefficient vector, the
squared modulus of the moment contraction is bounded by the concrete Gram
quadratic cost times the squared L2 norm of the test.  This is the
CompactLogTest-side shadow of the abstract minimum-norm theorem of record
1382. -/
theorem windowDual_le (f : CompactLogTest) {a b : ℝ} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b) {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) :
    ‖∑ i : ι, star (coeff i) * laplaceAt f (nodes i)‖ ^ 2 ≤
      (dotProduct (star coeff)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) coeff)).re
        * compactLogL2sq f := by
  classical
  have h := windowDual_integral_le f hab hsupp nodes coeff
  -- The cast Gram identity gives `Q.re = ∫‖W‖²` by taking real parts.
  have hq : (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume)
      = (dotProduct (star coeff)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) coeff)).re := by
    have hz := windowExpGram_quadratic_eq_integral a b nodes coeff
    rw [← hz, integral_norm_sq_re]
  rw [hq, norm_sq_windowIntegral_eq_compactLogL2sq f hab hsupp] at h
  exact h

/-- Same-owner interpolation cost lower bound: any compact-log test realizing
the node values `y` through a solved Gram system pays at least the (real,
nonnegative) Gram quadratic cost of the solve.  For a linearly independent
node family the best choice of `coeff` makes this bound `y* G⁻¹ y`, which is
exactly the N1c local-mass constant `K_loc` (record 1379, Lemma E).  This
theorem makes no existence, independence, or feasibility claim. -/
theorem windowExpGram_cost_le_compactLogL2sq (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) {ι : Type*}
    [Fintype ι] (nodes : ι → ℂ) (coeff y : ι → ℂ)
    (hvalues : ∀ i, laplaceAt f (nodes i) = y i)
    (hsolve : Matrix.mulVec (windowExpGramMatrix a b nodes) coeff = y) :
    (dotProduct (star coeff) y).re ≤ compactLogL2sq f := by
  classical
  have h := windowDual_le f hab hsupp nodes coeff
  rw [hsolve] at h
  have hc : ∑ i : ι, star (coeff i) * laplaceAt f (nodes i)
      = dotProduct (star coeff) y := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hvalues i]
    rfl
  have hqz : dotProduct (star coeff) y
      = (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
          * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume : ℂ) := by
    rw [← hsolve, ← windowExpGram_quadratic_eq_integral a b nodes coeff]
  rw [hc] at h
  rw [hqz] at h ⊢
  -- Rewriting both hypotheses with a two-item list would force the second
  -- item to fire on each target separately; the goal needs only the
  -- real-part normalization.
  rw [integral_norm_sq_re] at h ⊢
  rw [integral_norm_sq_cast] at h
  -- Note: Mathlib's `set` abstracts the value out of the goal by itself, so
  -- a following `rw [← hrdef] at ⊢` would find no occurrence. The closed
  -- form below works directly on the displayed window integral instead.
  have hbody : 0 ≤ ∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
      * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume := by
    refine intervalIntegral.integral_nonneg hab.le ?_
    intro x _
    exact sq_nonneg _
  have hC : 0 ≤ compactLogL2sq f := by
    unfold compactLogL2sq
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  -- The double ascription is essential: with the right-hand side in `ℝ` an
  -- unforced `↑(∫ ...)` inside the norm elaborates as the identity coercion
  -- `ℝ → ℝ` (invisible in the printed form), turning the statement into a
  -- real absolute value that `Complex.sq_norm` cannot match.
  have hcast : ‖((∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume : ℝ) : ℂ)‖ ^ 2
      = (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume)
      * (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume) := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
  rw [hcast] at h
  by_cases hbz : (∫ x : ℝ in a..b, ‖∑ i : ι, coeff i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume) = 0
  · rw [hbz] at h ⊢
    exact hC
  · exact le_of_mul_le_mul_left h
      (lt_of_le_of_ne hbody (Ne.symm hbz))

/-- The exact nonzero-frequency closed form of the window Gram entry.  The
division is legitimate only under the explicit frequency-nonzero premise. -/
theorem windowExpGram_of_ne_zero (a b : ℝ) (s t : ℂ) (hlam : s + star t ≠ 0) :
    windowExpGram a b s t =
      (Complex.exp ((s + star t) * (b : ℂ)) - Complex.exp ((s + star t) * (a : ℂ)))
        / (s + star t) := by
  unfold windowExpGram
  have hF : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t))
      (Complex.exp ((s + star t) * (x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (s + star t) * (y : ℂ))
        (s + star t) x := by
      have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
        Complex.ofRealCLM.hasDerivAt
      convert h0.const_smul (s + star t) using 1
      all_goals simp [smul_eq_mul]
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)))
        (Complex.exp ((s + star t) * (x : ℂ)) * (s + star t)) x :=
      (Complex.hasDerivAt_exp ((s + star t) * (x : ℂ))).comp x h1
    convert h2.div_const (s + star t) using 1
    · field_simp [hlam]
  have hc : Continuous fun x : ℝ => Complex.exp ((s + star t) * (x : ℂ)) := by
    continuity
  have hint : IntervalIntegrable (fun x : ℝ =>
      Complex.exp ((s + star t) * (x : ℂ))) volume a b :=
    hc.intervalIntegrable a b
  have hsub :
      (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t)) b
        - (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t)) a
        = (Complex.exp ((s + star t) * (b : ℂ))
            - Complex.exp ((s + star t) * (a : ℂ))) / (s + star t) := by
    show (Complex.exp ((s + star t) * (b : ℂ)) / (s + star t)
        - Complex.exp ((s + star t) * (a : ℂ)) / (s + star t))
        = (Complex.exp ((s + star t) * (b : ℂ))
            - Complex.exp ((s + star t) * (a : ℂ))) / (s + star t)
    field_simp [hlam]
  -- The membership binder must be written by hand: at the lemma argument
  -- position the endpoint and derivative metas are still open when `hF` is
  -- checked, so Lean does not insert the unused hypothesis.
  have hF' : ∀ x ∈ Set.uIcc a b, HasDerivAt
      (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t))
      ((fun z : ℝ => Complex.exp ((s + star t) * (z : ℂ))) x) x :=
    fun x _ => hF x
  have hI : ∫ x : ℝ in a..b, Complex.exp ((s + star t) * (x : ℂ)) ∂volume
      = (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t)) b
        - (fun y : ℝ => Complex.exp ((s + star t) * (y : ℂ)) / (s + star t)) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF' hint
  rw [hI]
  exact hsub

/-- The zero-frequency closed form: the entry degenerates to the window
width, mirroring the critical-line diagonal of record 1382. -/
theorem windowExpGram_of_zero (a b : ℝ) (s t : ℂ) (hlam : s + star t = 0) :
    windowExpGram a b s t = (b - a : ℂ) := by
  unfold windowExpGram
  -- The pointwise degeneracy first (the right-hand side is a scalar, so a
  -- congruence lemma has to produce the integral-of-one intermediate):
  calc ∫ x : ℝ in a..b, Complex.exp ((s + star t) * (x : ℂ)) ∂volume
      = ∫ x : ℝ in a..b, (1 : ℂ) ∂volume := by
          -- The `refine` first fixes the congruence's function metavariables;
          -- a bare `by simp [hlam]` in argument position sees unresolved
          -- metavariables and silently uses no hypothesis.
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          rw [hlam, zero_mul, Complex.exp_zero]
    _ = (b - a : ℂ) := by
          rw [intervalIntegral.integral_const]
          simp [Algebra.smul_def]

end C1WindowMellinGram
end Source
end ConnesWeilRH
