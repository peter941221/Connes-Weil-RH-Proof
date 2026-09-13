/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowMellinGram

/-!
# C1WindowMellinIndependence - the 2c tail: independence, nonsingularity, K_loc

The 2c-core leaf `C1WindowMellinGram` proved the cost comparison
`(star coeff ⬝ᵥ y).re ≤ compactLogL2sq f` for every *solved* Gram system.
This leaf completes the tail promised by the record-1383 scope note:

1. linear independence of the window exponential family - proved from
   scratch by a `Finset` induction whose step shifts the vanishing
   combination by `exp (-nodesⱼ x)`, then kills the remaining analytic
   combination by pointwise differentiation and the uniqueness of the
   derivative; there is deliberately no Mathlib `linearIndependent_exp`
   (none exists) and no Vandermonde determinant route (the Gram entries
   here are window integrals, not pure powers);
2. the continuous-nonneg window-integral-zero pointwise lemma, the
   bridge from a vanishing Gram quadratic form to a vanishing
   combination;
3. trivial kernel and hence `IsUnit` of the concrete window Gram matrix
   for distinct nodes (via `Matrix.mulVec_injective_iff_isUnit`);
4. the `K_loc` instantiation of the 2c-core cost comparison at the
   inverse solve `coeff = G⁻¹ y` (record 1379, Lemma E).

All statements stay on the genuine `CompactLogTest` owner with raw
interval integrals; the `Lp` a.e.-quotient API is not touched, and no
floating-point evidence enters any proof.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 1.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowMellinIndependence

open MeasureTheory
open Filter
open scoped Topology
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinGram

/-- Pointwise derivative of a pure complex exponential along the real
axis: the analytic kernel of the independence induction. -/
theorem hasDerivAt_exp_mul_coe (μ : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (μ * (y : ℂ)))
      (μ * Complex.exp (μ * (x : ℂ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => μ * (y : ℂ)) μ x := by
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
      Complex.ofRealCLM.hasDerivAt
    convert h0.const_smul μ using 1
    all_goals simp [smul_eq_mul]
  convert (Complex.hasDerivAt_exp (μ * (x : ℂ))).comp x h1 using 1
  ring

/-- Vanishing window combination of distinct exponentials forces vanishing
coefficients: the linear independence of the concrete Mellin representer
family on any open window.  The induction over the node `Finset` shifts by
the removed node's exponential, differentiates the remainder at an interior
point (uniqueness of the derivative against the constant function), and
falls to the induction hypothesis for the pairwise-distinct difference
family.  `nodes` and `c` are quantified inside the motive because the step
re-instantiates the theorem at the difference family. -/
theorem finiteExp_windowComb_eq_zero {ι : Type*} (S : Finset ι) {a b : ℝ}
    (hab : a < b) :
    ∀ (nodes : ι → ℂ) (c : ι → ℂ),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → nodes i ≠ nodes j) →
      (∀ x ∈ Set.Ioo a b,
          ∑ i ∈ S, c i * Complex.exp (nodes i * (x : ℂ)) = 0) →
      ∀ i ∈ S, c i = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro nodes c hne hz i hi
      exact absurd hi (by simp)
  | @insert j s hj ih =>
      intro nodes c hne hz
      -- The shifted identity: `c j + Σᵢ∈ₛ cᵢ exp((nodes i - nodes j) x) = 0`
      -- on the window; the multiplier `exp (-nodes j · x)` never vanishes.
      have hshift : ∀ x ∈ Set.Ioo a b,
          c j + ∑ i ∈ s, c i * Complex.exp ((nodes i - nodes j) * (x : ℂ)) = 0 := by
        intro x hx
        have hsub : (∑ i ∈ s, c i * Complex.exp (nodes i * (x : ℂ)))
            = -(c j * Complex.exp (nodes j * (x : ℂ))) := by
          have hx0 := hz x hx
          -- `eq_neg_of_add_eq_zero_left` is `a + b = 0 → a = -b`;
          -- `Finset.sum_insert` prepends the new term, so commute first.
          rw [Finset.sum_insert hj, add_comm] at hx0
          exact eq_neg_of_add_eq_zero_left hx0
        have hsum : (∑ i ∈ s, c i * Complex.exp ((nodes i - nodes j) * (x : ℂ)))
            = -(c j) := by
          calc (∑ i ∈ s, c i * Complex.exp ((nodes i - nodes j) * (x : ℂ)))
              = ∑ i ∈ s, c i * (Complex.exp (nodes i * (x : ℂ))
                  * Complex.exp (- (nodes j * (x : ℂ)))) := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [sub_mul, sub_eq_add_neg, Complex.exp_add]
            _ = Complex.exp (- (nodes j * (x : ℂ)))
                  * ∑ i ∈ s, c i * Complex.exp (nodes i * (x : ℂ)) := by
                refine (Finset.sum_congr rfl
                  fun i _ => (mul_assoc _ _ _).symm).trans ?_
                rw [← Finset.sum_mul, mul_comm]
            _ = Complex.exp (- (nodes j * (x : ℂ)))
                  * -(c j * Complex.exp (nodes j * (x : ℂ))) := by rw [hsub]
            _ = -(c j * (Complex.exp (- (nodes j * (x : ℂ)))
                  * Complex.exp (nodes j * (x : ℂ)))) := by ring
            _ = -(c j) := by
                rw [← Complex.exp_add]
                simp
        rw [hsum]
        ring
      -- Pairwise separation of the difference family on `s`.
      have hne' : ∀ i ∈ s, ∀ k ∈ s, i ≠ k →
          nodes i - nodes j ≠ nodes k - nodes j := by
        intro i hi k hk hik h
        have hd : nodes i - nodes k = 0 := by
          have h2 : nodes i - nodes k
              = (nodes i - nodes j) - (nodes k - nodes j) := by ring
          rw [h2, h, sub_self]
        exact hne i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk) hik
          (sub_eq_zero.mp hd)
      -- The differentiated identity on the window: uniqueness of the
      -- derivative against the constant function `-(c j)`.
      have hderiv0 : ∀ x ∈ Set.Ioo a b,
          ∑ i ∈ s, c i * ((nodes i - nodes j)
              * Complex.exp ((nodes i - nodes j) * (x : ℂ))) = 0 := by
        intro x₀ hx₀
        have hF : HasDerivAt (fun y : ℝ => ∑ i ∈ s,
            c i * Complex.exp ((nodes i - nodes j) * (y : ℂ)))
            (∑ i ∈ s, c i * ((nodes i - nodes j)
              * Complex.exp ((nodes i - nodes j) * (x₀ : ℂ)))) x₀ :=
          HasDerivAt.fun_sum fun i _ =>
            (hasDerivAt_exp_mul_coe (nodes i - nodes j) x₀).const_mul (c i)
        have hev : (fun _ : ℝ => -(c j))
            =ᶠ[𝓝 x₀] (fun y : ℝ => ∑ i ∈ s,
              c i * Complex.exp ((nodes i - nodes j) * (y : ℂ))) := by
          filter_upwards [isOpen_Ioo.mem_nhds hx₀] with y hy
          have h2 : (∑ i ∈ s, c i * Complex.exp ((nodes i - nodes j) * (y : ℂ)))
              + c j = 0 := by rw [add_comm]; exact hshift y hy
          exact (eq_neg_of_add_eq_zero_left h2).symm
        have hzero : HasDerivAt (fun _ : ℝ => -(c j))
            (∑ i ∈ s, c i * ((nodes i - nodes j)
              * Complex.exp ((nodes i - nodes j) * (x₀ : ℂ)))) x₀ :=
          hF.congr_of_eventuallyEq hev
        exact hzero.unique (hasDerivAt_const x₀ (-(c j)))
      -- Reassociate to the induction-hypothesis shape and recurse.
      have hz' : ∀ x ∈ Set.Ioo a b,
          ∑ i ∈ s, (c i * (nodes i - nodes j))
              * Complex.exp ((nodes i - nodes j) * (x : ℂ)) = 0 := by
        intro x hx
        have hdx := hderiv0 x hx
        rw [← hdx]
        exact Finset.sum_congr rfl (fun i _ => mul_assoc _ _ _)
      have hc0 : ∀ i ∈ s, c i = 0 := by
        intro i hi
        have h1 := ih (fun k => nodes k - nodes j) (fun k => c k * (nodes k - nodes j))
          hne' hz' i hi
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exfalso
          have hij : i ≠ j := fun heq => hj (heq ▸ hi)
          have hneij : nodes i ≠ nodes j :=
            hne i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j s) hij
          exact sub_ne_zero.mpr hneij h
      -- The conclusion, with the removed coefficient killed by the value
      -- identity at any interior point (the window is nonempty as `a < b`).
      intro i hi
      simp only [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · obtain ⟨x₀, hx₀⟩ := Set.nonempty_Ioo.mpr hab
        have h1 := hshift x₀ hx₀
        rw [Finset.sum_eq_zero (fun k hk => by rw [hc0 k hk]; simp)] at h1
        simpa using h1
      · exact hc0 i hi

/-- A continuous nonnegative function with zero window integral vanishes at
every interior point.  This is the bridge from a vanishing Gram quadratic
form to a pointwise-vanishing representer combination.  The engine is
`intervalIntegral.integral_pos`: a continuous function strictly positive at
one interior point has strictly positive window integral, so the interior
zero set of a nonnegative null integrand is everything. -/
theorem continuous_nonneg_windowIntegral_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Continuous f) (h₀ : ∫ x : ℝ in a..b, f x ∂volume = 0)
    (hn : ∀ x ∈ Set.uIcc a b, 0 ≤ f x) : ∀ x ∈ Set.Ioo a b, f x = 0 := by
  intro x₀ hx₀
  by_contra hne
  have hpos : 0 < f x₀ :=
    lt_of_le_of_ne (hn x₀ (show min a b ≤ x₀ ∧ x₀ ≤ max a b from
      ⟨le_trans (min_le_left a b) (le_of_lt hx₀.1),
        le_trans (le_of_lt hx₀.2) (le_max_right a b)⟩))
      (Ne.symm hne)
  have h1 : 0 < ∫ x : ℝ in a..b, f x ∂volume :=
    intervalIntegral.integral_pos hab hf.continuousOn
      (fun y hy => hn y (show min a b ≤ y ∧ y ≤ max a b from
        ⟨le_trans (min_le_left a b) (le_of_lt hy.1),
          le_trans hy.2 (le_max_right a b)⟩))
      ⟨x₀, ⟨le_of_lt hx₀.1, le_of_lt hx₀.2⟩, hpos⟩
  rw [h₀] at h1
  exact lt_irrefl 0 h1

/-- Trivial kernel of the concrete window Gram matrix for distinct nodes:
a right-null coefficient vector must vanish, because its Gram quadratic
form is the window integral of a squared modulus, which vanishes pointwise
by the continuous-nonneg lemma, and the exponential family is
window-independent. -/
theorem windowExpGramMatrix_mulVec_eq_zero {ι : Type*} [Fintype ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (hne : Function.Injective nodes) (v : ι → ℂ)
    (hv : Matrix.mulVec (windowExpGramMatrix a b nodes) v = 0) : v = 0 := by
  -- The cast Gram quadratic form vanishes.
  have hz : (∫ x : ℝ in a..b, ‖∑ i : ι, v i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume : ℂ) = 0 := by
    have hq := windowExpGram_quadratic_eq_integral a b nodes v
    rw [hv, dotProduct_zero] at hq
    exact hq
  -- Taking real parts: the real window integral of the squared modulus
  -- vanishes.
  have hzero : ∫ x : ℝ in a..b, ‖∑ i : ι, v i
      * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume = 0 := by
    have hre := congrArg Complex.re hz
    rw [integral_norm_sq_re, Complex.zero_re] at hre
    exact hre
  -- Pointwise vanishing of the combination on the window.
  have hc : Continuous (fun x : ℝ =>
      ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2) := by
    continuity
  have hpt : ∀ x ∈ Set.Ioo a b, ‖∑ i : ι, v i
      * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 = 0 :=
    continuous_nonneg_windowIntegral_zero hab hc hzero
      (fun x _ => sq_nonneg _)
  have hsum : ∀ x ∈ Set.Ioo a b,
      ∑ i ∈ Finset.univ, v i * Complex.exp (star (nodes i) * (x : ℂ)) = 0 := by
    intro x hx
    have h2 : ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖
          * ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖ = 0 := by
      rw [← pow_two]
      exact hpt x hx
    exact norm_eq_zero.mp (eq_zero_of_mul_self_eq_zero h2)
  -- The independence induction at the family `star ∘ nodes` and `S = univ`.
  have hne' : ∀ p ∈ (Finset.univ : Finset ι), ∀ q ∈ (Finset.univ : Finset ι),
      p ≠ q → star (nodes p) ≠ star (nodes q) := by
    intro p _ q _ hpq h
    exact hpq (hne (star_injective h))
  refine funext fun i => finiteExp_windowComb_eq_zero Finset.univ hab
    (fun p => star (nodes p)) v hne' hsum i (Finset.mem_univ i)

/-- The concrete window Gram matrix is invertible for distinct nodes.  This
is the branch that record 1382's rank-deficient split left open; the
rank-deficient branch itself can now only occur for coinciding nodes. -/
theorem windowExpGramMatrix_isUnit_of_injective {ι : Type*} [Fintype ι]
    [DecidableEq ι] {a b : ℝ} (hab : a < b) (nodes : ι → ℂ)
    (hne : Function.Injective nodes) :
    IsUnit (windowExpGramMatrix a b nodes) := by
  -- `A` is pinned explicitly: with a hole, the `Fintype` instance of the
  -- index type stays a metavariable and resolution refuses to run.
  -- Note the direction: `Iff.mp : Injective → IsUnit` here (the iff reads
  -- `Injective ↔ IsUnit`, so `.mpr` goes the other way).
  refine (Matrix.mulVec_injective_iff_isUnit
      (A := windowExpGramMatrix a b nodes)).mp ?_
  intro u v huv
  apply sub_eq_zero.mp
  refine windowExpGramMatrix_mulVec_eq_zero hab nodes hne (u - v) ?_
  have h0 : Matrix.mulVec (windowExpGramMatrix a b nodes) (u - v)
      = Matrix.mulVec (windowExpGramMatrix a b nodes) u
          - Matrix.mulVec (windowExpGramMatrix a b nodes) v := by
    -- The `show` carries the definitional unfolding of `mulVecLin` (its
    -- `toFun` is `mulVec`); `simpa only [mulVecLin_apply]` leaves the
    -- index-type metavariable of the `Fintype` instance stuck.
    show ⇑(Matrix.mulVecLin (windowExpGramMatrix a b nodes)) (u - v)
        = ⇑(Matrix.mulVecLin (windowExpGramMatrix a b nodes)) u
            - ⇑(Matrix.mulVecLin (windowExpGramMatrix a b nodes)) v
    exact (Matrix.mulVecLin (windowExpGramMatrix a b nodes)).map_sub u v
  rw [h0, huv, sub_self]

/-- The `K_loc` instantiation in hypothesis form (record 1379, Lemma E):
whenever the window Gram matrix is a unit, the inverse-solve cost
`(star (G⁻¹ y) ⬝ᵥ y).re` lower-bounds the squared L2 norm of every
compact-log test that realizes the values `y` on the nodes.  The
invertibility is an explicit premise (not a `let` binding) so the proof
term never enters the statement type; the value-realization hypothesis is
the open analytic interface inherited from the orbit package, and no
numeric margin or feasibility claim is made here. -/
theorem solvedWindowGram_cost_le_compactLogL2sq (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (nodes : ι → ℂ) (y : ι → ℂ)
    (hG : IsUnit (windowExpGramMatrix a b nodes))
    (hvalues : ∀ i, laplaceAt f (nodes i) = y i) :
    (dotProduct (star (Matrix.mulVec ↑hG.unit⁻¹ y)) y).re
      ≤ compactLogL2sq f := by
  -- The solve is established as a standalone fact first: feeding it as a
  -- `refine` hole forces the elaborator to whnf the substituted matrix
  -- product inside the huge cost-theorem application and exhausts the
  -- heartbeat budget.
  have hsolve : Matrix.mulVec (windowExpGramMatrix a b nodes)
      (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y) = y := by
    calc Matrix.mulVec (windowExpGramMatrix a b nodes)
            (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y)
        = Matrix.mulVec (windowExpGramMatrix a b nodes
            * (↑hG.unit⁻¹ : Matrix ι ι ℂ)) y :=
            -- Explicit `M`/`N` pins the index-type metavariables of the
            -- `Fintype` instances; with holes the instance search hangs the
            -- elaborator into the heartbeat limit.  The stated direction is
            -- `M.mulVec (N.mulVec v) = (M * N).mulVec v` (no `.symm`).
            Matrix.mulVec_mulVec y (windowExpGramMatrix a b nodes)
              (↑hG.unit⁻¹ : Matrix ι ι ℂ)
      _ = Matrix.mulVec (1 : Matrix ι ι ℂ) y := by rw [hG.mul_val_inv]
      _ = y := Matrix.one_mulVec y
  exact windowExpGram_cost_le_compactLogL2sq f hab hsupp nodes
    (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y) y hvalues hsolve

/-- The `K_loc` corollary: for a pairwise-distinct node family the inverse
exists by the nonsingularity theorem, so the concrete local-mass quantity
`y* G⁻¹ y` is a certified lower bound of the test's squared L2 cost. -/
theorem windowGramInverse_cost_le_compactLogL2sq (f : CompactLogTest) {a b : ℝ}
    (hab : a < b) (hsupp : Function.support f.test ⊆ Set.Ioo a b) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (nodes : ι → ℂ) (y : ι → ℂ)
    (hne : Function.Injective nodes)
    (hvalues : ∀ i, laplaceAt f (nodes i) = y i) :
    (dotProduct (star (Matrix.mulVec
        ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹ y)) y).re
      ≤ compactLogL2sq f :=
  solvedWindowGram_cost_le_compactLogL2sq f hab hsupp nodes y
    (windowExpGramMatrix_isUnit_of_injective hab nodes hne) hvalues

end C1WindowMellinIndependence
end Source
end ConnesWeilRH
