/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowMellinIndependence

/-!
# C1WindowTaperCore - the corrected finite system (N2beta component 3, core)

Records 1382-1384 built the exact cost lower bound `K_loc ≤ compactLogL2sq f`
for owner tests realizing node values through a solved window Gram system.
The smooth lift (ladder item 3) replaces the indicator-window representer
family by its taper-weighted twin.  This core leaf sets up that corrected
finite system and proves it is exactly solvable:

- the taper-weighted moment Gram `windowTaperGramMatrix` of entries
  `∫ x in a..b, τ x * exp ((s + star t) * x)`;
- its concrete quadratic identity (weighted window integral of the squared
  modulus of the representer combination), and the real-weight `re` form;
- trivial kernel for distinct nodes: a null vector's vanishing weighted
  integral, the record-1384 pointwise bridge, the taper-one sub-window, and
  record-1384 independence at `star ∘ nodes` kill it; hence invertibility,
  so the corrected system `T · c = y` is solved exactly by `c = T⁻¹ y`;
- the unweighted pairing identity and its Cauchy-Schwarz between two window
  representer combinations, the inequality used by the lift's budget.

No owner construction, no numeric taper parameters, no budget claim yet: that
is the paired leaf `C1WindowTaperLift`.  RH is not claimed.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md, item 3.
-/

namespace ConnesWeilRH
namespace Source
namespace C1WindowTaperCore

open MeasureTheory
open scoped Topology
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinGram
open C1WindowMellinIndependence

/-- The representer combination `x ↦ Σ i, coeff i * exp (star (nodes i) * x)`
at the `star`-conjugated nodes: the same shape the 2c-core quadratic
identity integrates. -/
noncomputable def windowTaperComb {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (coeff : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))

/-- The taper-weighted window moment Gram entry: the `τ`-weighted integral of
the pairing exponential.  `τ = 1` recovers `windowExpGram`. -/
noncomputable def windowTaperGram (a b : ℝ) (τ : ℝ → ℂ) (s t : ℂ) : ℂ :=
  ∫ x : ℝ in a..b, τ x * Complex.exp ((s + star t) * (x : ℂ)) ∂volume

/-- The taper-weighted moment Gram matrix of a finite node family. -/
noncomputable def windowTaperGramMatrix {ι : Type*} [Fintype ι]
    (a b : ℝ) (τ : ℝ → ℂ) (nodes : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => windowTaperGram a b τ (nodes i) (nodes j)

/-! ### Quadratic identities -/

/-- The tapered Gram quadratic identity: the weighted window integral of the
squared modulus of the representer combination is exactly the plain-bilinear
tapered-Gram quadratic `star coeff ⬝ᵥ (T · coeff)`. -/
theorem windowTaperGram_quadratic_eq_integral {ι : Type*} [Fintype ι]
    (a b : ℝ) (τ : ℝ → ℂ) (hτc : Continuous τ) (nodes : ι → ℂ) (coeff : ι → ℂ) :
    (∫ x : ℝ in a..b,
          τ x * (‖windowTaperComb nodes coeff x‖ ^ 2 : ℂ) ∂volume) =
      dotProduct (star coeff)
        (Matrix.mulVec (windowTaperGramMatrix a b τ nodes) coeff) := by
  classical
  have hpoint : ∀ x : ℝ,
      τ x * (‖windowTaperComb nodes coeff x‖ ^ 2 : ℂ)
        = ∑ i : ι, ∑ j : ι,
            star (coeff i)
              * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)))
                  * coeff j) := by
    intro x
    have hsqz (z : ℂ) : (‖z‖ : ℂ) ^ 2 = star z * z := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      rfl
    have hconj : star (windowTaperComb nodes coeff x)
        = ∑ i : ι, star (coeff i) * Complex.exp (nodes i * (x : ℂ)) := by
      show star (∑ i : ι, coeff i * Complex.exp (star (nodes i) * (x : ℂ))) = _
      rw [star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hse (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) :=
        (Complex.exp_conj z).symm
      have hx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
      rw [star_mul', hse, star_mul', star_star, hx]
    have hinner : star (windowTaperComb nodes coeff x)
        * windowTaperComb nodes coeff x
        = ∑ i : ι, ∑ j : ι,
            (star (coeff i) * Complex.exp (nodes i * (x : ℂ)))
              * (coeff j * Complex.exp (star (nodes j) * (x : ℂ))) := by
      rw [hconj]
      simp only [windowTaperComb]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    rw [hsqz, hinner, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hmerge : Complex.exp (nodes i * (x : ℂ))
        * Complex.exp (star (nodes j) * (x : ℂ))
        = Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc τ x * ((star (coeff i) * Complex.exp (nodes i * (x : ℂ)))
            * (coeff j * Complex.exp (star (nodes j) * (x : ℂ))))
        = star (coeff i) * coeff j * (τ x
            * (Complex.exp (nodes i * (x : ℂ))
                * Complex.exp (star (nodes j) * (x : ℂ)))) := by ring
      _ = star (coeff i) * coeff j * (τ x
            * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))) := by rw [hmerge]
      _ = star (coeff i)
            * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)))
                * coeff j) := by ring
  simp only [windowTaperGram, windowTaperGramMatrix,
    Matrix.mulVec, dotProduct]
  refine (intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun x _ => hpoint x)).trans ?_
  refine (intervalIntegral.integral_finsetSum ?_).trans ?_
  · intro i _
    have hc : Continuous fun x : ℝ => ∑ j : ι,
        star (coeff i)
          * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))) * coeff j) := by
          continuity
    exact hc.intervalIntegrable a b
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : ∀ j ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun x : ℝ => star (coeff i)
          * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))) * coeff j))
        volume a b := by
      intro j _
      have hc : Continuous (fun x : ℝ => star (coeff i)
          * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))) * coeff j)) := by
          continuity
      exact hc.intervalIntegrable a b
    have hj (j : ι) : ∫ x : ℝ in a..b, star (coeff i)
          * ((τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ))) * coeff j) ∂volume
        = star (coeff i)
            * ((∫ x : ℝ in a..b,
                τ x * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) ∂volume)
                * coeff j) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    exact ((intervalIntegral.integral_finsetSum hf).trans
        (Finset.sum_congr rfl fun j _ => hj j)).trans
      (Finset.mul_sum _ _ _).symm

/-- Real-taper form: for a real weight the real part of the tapered quadratic
is the plain real weighted window integral of the squared modulus. -/
theorem windowTaperGram_quadratic_re {ι : Type*} [Fintype ι]
    (a b : ℝ) (τ : ℝ → ℝ) (hτc : Continuous τ) (nodes : ι → ℂ) (coeff : ι → ℂ) :
    (dotProduct (star coeff)
        (Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) coeff)).re
      = ∫ x : ℝ in a..b, τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume := by
  classical
  have hz := windowTaperGram_quadratic_eq_integral a b (fun x => (τ x : ℂ))
    (Complex.continuous_ofReal.comp hτc) nodes coeff
  have hcast : (∫ x : ℝ in a..b,
        (τ x : ℂ) * (‖windowTaperComb nodes coeff x‖ ^ 2 : ℂ) ∂volume)
      = ↑(∫ x : ℝ in a..b, τ x * ‖windowTaperComb nodes coeff x‖ ^ 2 ∂volume) := by
    refine (intervalIntegral.integral_congr (fun x _ => ?_)).trans
      (intervalIntegral.integral_ofReal (μ := volume))
    have hp : ((‖windowTaperComb nodes coeff x‖ : ℂ) ^ 2)
        = ((‖windowTaperComb nodes coeff x‖ ^ 2 : ℝ) : ℂ) :=
      (Complex.ofReal_pow _ 2).symm
    rw [hp, Complex.ofReal_mul]
  rw [← hz, hcast, Complex.ofReal_re]

/-! ### Trivial kernel and invertibility of the corrected system -/

/-- The corrected (taper-weighted) moment system has trivial kernel whenever
the real taper is nonnegative, continuous, equals one on a sub-window, and
the nodes are distinct.  The chain is: null vector -> vanishing weighted
integral -> record-1384 pointwise bridge -> the combination vanishes on the
sub-window -> record-1384 independence at `star ∘ nodes`. -/
theorem windowTaperGramMatrix_mulVec_eq_zero {ι : Type*} [Fintype ι]
    {a b : ℝ} (hab : a < b) (τ : ℝ → ℝ) (hτc : Continuous τ) (hτ0 : ∀ x, 0 ≤ τ x)
    {a' b' : ℝ} (ha'b' : a' < b') (hsub : Set.Ioo a' b' ⊆ Set.Ioo a b)
    (hτ1 : ∀ x ∈ Set.Ioo a' b', τ x = 1)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (v : ι → ℂ)
    (hv : Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) v = 0) :
    v = 0 := by
  classical
  have hq : (dotProduct (star v)
      (Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) v)).re = 0 := by
    rw [hv, dotProduct_zero, Complex.zero_re]
  have hz : ∫ x : ℝ in a..b, τ x * ‖windowTaperComb nodes v x‖ ^ 2 ∂volume = 0 := by
    rw [← windowTaperGram_quadratic_re a b τ hτc nodes v, hq]
  have hW : Continuous (fun x : ℝ => τ x * ‖windowTaperComb nodes v x‖ ^ 2) := by
    refine hτc.mul ?_
    show Continuous (fun x : ℝ =>
      ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2)
    continuity
  have hnonneg : ∀ x ∈ Set.uIcc a b, 0 ≤ τ x * ‖windowTaperComb nodes v x‖ ^ 2 := by
    intro x _
    exact mul_nonneg (hτ0 x) (sq_nonneg _)
  have hpt := continuous_nonneg_windowIntegral_zero hab hW hz hnonneg
  have hsum : ∀ x ∈ Set.Ioo a' b',
      ∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ)) = 0 := by
    intro x hx
    have h1 : τ x * ‖windowTaperComb nodes v x‖ ^ 2 = 0 := hpt x (hsub hx)
    rw [hτ1 x hx, one_mul] at h1
    have h2 : ‖windowTaperComb nodes v x‖ * ‖windowTaperComb nodes v x‖ = 0 := by
      rw [← pow_two]
      exact h1
    have h3 : windowTaperComb nodes v x = 0 :=
      norm_eq_zero.mp (eq_zero_of_mul_self_eq_zero h2)
    simpa [windowTaperComb] using h3
  refine funext fun i => finiteExp_windowComb_eq_zero Finset.univ ha'b'
    (fun p => star (nodes p)) v
    (fun i hi j hj hij hpq => hij (hne (star_injective hpq)))
    hsum i (Finset.mem_univ i)

/-- The corrected finite system is exactly solvable: under the same
hypotheses the tapered moment Gram is invertible. -/
theorem windowTaperGramMatrix_isUnit_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ℝ} (hab : a < b) (τ : ℝ → ℝ) (hτc : Continuous τ) (hτ0 : ∀ x, 0 ≤ τ x)
    {a' b' : ℝ} (ha'b' : a' < b') (hsub : Set.Ioo a' b' ⊆ Set.Ioo a b)
    (hτ1 : ∀ x ∈ Set.Ioo a' b', τ x = 1)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) :
    IsUnit (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) := by
  classical
  refine (Matrix.mulVec_injective_iff_isUnit
      (A := windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)).mp ?_
  intro u v huv
  apply sub_eq_zero.mp
  refine windowTaperGramMatrix_mulVec_eq_zero hab τ hτc hτ0 ha'b' hsub hτ1
    nodes hne (u - v) ?_
  have h0 : Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) (u - v)
      = Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) u
        - Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) v := by
    show ⇑(Matrix.mulVecLin
        (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)) (u - v)
      = ⇑(Matrix.mulVecLin
          (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)) u
        - ⇑(Matrix.mulVecLin
            (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)) v
    exact (Matrix.mulVecLin
      (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)).map_sub u v
  rw [h0, huv, sub_self]

/-- The solved tapered system realizes every node value: `T · (T⁻¹ y) = y`,
the exact correction system the lift assembles around. -/
theorem windowTaperGram_solve_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ℝ} (hab : a < b) (τ : ℝ → ℝ) (hτc : Continuous τ) (hτ0 : ∀ x, 0 ≤ τ x)
    {a' b' : ℝ} (ha'b' : a' < b') (hsub : Set.Ioo a' b' ⊆ Set.Ioo a b)
    (hτ1 : ∀ x ∈ Set.Ioo a' b', τ x = 1)
    (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ) :
    Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)
        (Matrix.mulVec
          ↑(windowTaperGramMatrix_isUnit_of_injective hab τ hτc hτ0 ha'b' hsub hτ1
            nodes hne).unit⁻¹
          y) = y := by
  classical
  set hT : IsUnit (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes) :=
    windowTaperGramMatrix_isUnit_of_injective hab τ hτc hτ0 ha'b' hsub hτ1 nodes hne
  calc Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)
        (Matrix.mulVec (↑hT.unit⁻¹ : Matrix ι ι ℂ) y)
      = Matrix.mulVec (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes
          * (↑hT.unit⁻¹ : Matrix ι ι ℂ)) y :=
          -- Pinned `M`/`N` args and the no-`.symm` stated direction
          -- `M.mulVec (N.mulVec v) = (M * N).mulVec v` (1384 companion).
          Matrix.mulVec_mulVec y
            (windowTaperGramMatrix a b (fun x => (τ x : ℂ)) nodes)
            (↑hT.unit⁻¹ : Matrix ι ι ℂ)
    _ = Matrix.mulVec (1 : Matrix ι ι ℂ) y := by rw [hT.mul_val_inv]
    _ = y := Matrix.one_mulVec y

/-! ### Unweighted pairing and its Cauchy-Schwarz -/

/-- The unweighted pairing identity: `star u ⬝ᵥ (A · v)` is the window
integral of `star (U_u x) * U_v x`. -/
theorem windowExpGram_pairing_eq_integral {ι : Type*} [Fintype ι]
    (a b : ℝ) (nodes : ι → ℂ) (u v : ι → ℂ) :
    (∫ x : ℝ in a..b,
        star (windowTaperComb nodes u x) * windowTaperComb nodes v x ∂volume)
      = dotProduct (star u) (Matrix.mulVec (windowExpGramMatrix a b nodes) v) := by
  classical
  have hpoint : ∀ x : ℝ,
      star (windowTaperComb nodes u x) * windowTaperComb nodes v x
        = ∑ i : ι, ∑ j : ι,
            star (u i) * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j) := by
    intro x
    have hconj : star (windowTaperComb nodes u x)
        = ∑ i : ι, star (u i) * Complex.exp (nodes i * (x : ℂ)) := by
      show star (∑ i : ι, u i * Complex.exp (star (nodes i) * (x : ℂ))) = _
      rw [star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hse (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) :=
        (Complex.exp_conj z).symm
      have hx : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
      rw [star_mul', hse, star_mul', star_star, hx]
    rw [hconj]
    simp only [windowTaperComb]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hmerge : Complex.exp (nodes i * (x : ℂ))
        * Complex.exp (star (nodes j) * (x : ℂ))
        = Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc star (u i) * Complex.exp (nodes i * (x : ℂ))
            * (v j * Complex.exp (star (nodes j) * (x : ℂ)))
        = star (u i) * v j
            * (Complex.exp (nodes i * (x : ℂ))
                * Complex.exp (star (nodes j) * (x : ℂ))) := by ring
      _ = star (u i) * v j
            * Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) := by rw [hmerge]
      _ = star (u i)
            * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j) := by ring
  simp only [windowExpGram, windowExpGramMatrix,
    Matrix.mulVec, dotProduct]
  refine (intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun x _ => hpoint x)).trans ?_
  refine (intervalIntegral.integral_finsetSum ?_).trans ?_
  · intro i _
    have hc : Continuous fun x : ℝ => ∑ j : ι,
        star (u i) * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j) := by
          continuity
    exact hc.intervalIntegrable a b
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : ∀ j ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun x : ℝ => star (u i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j))
        volume a b := by
      intro j _
      have hc : Continuous (fun x : ℝ => star (u i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j)) := by
          continuity
      exact hc.intervalIntegrable a b
    have hj (j : ι) : ∫ x : ℝ in a..b, star (u i)
          * (Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) * v j) ∂volume
        = star (u i)
            * ((∫ x : ℝ in a..b,
                Complex.exp ((nodes i + star (nodes j)) * (x : ℂ)) ∂volume) * v j) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    exact ((intervalIntegral.integral_finsetSum hf).trans
        (Finset.sum_congr rfl fun j _ => hj j)).trans
      (Finset.mul_sum _ _ _).symm

/-- Pairing Cauchy-Schwarz between two window representer combinations: the
squared modulus of the cross quadratic `star u ⬝ᵥ (A · v)` is bounded by the
product of the two real window energies. -/
theorem windowExpGram_pairing_csq {ι : Type*} [Fintype ι]
    (a b : ℝ) {hab : a < b} (nodes : ι → ℂ) (u v : ι → ℂ) :
    ‖dotProduct (star u) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)‖ ^ 2
      ≤ (dotProduct (star u) (Matrix.mulVec (windowExpGramMatrix a b nodes) u)).re
        * (dotProduct (star v) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by
  classical
  have hpair : dotProduct (star u) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)
      = ∫ x : ℝ in a..b,
          star (windowTaperComb nodes u x) * windowTaperComb nodes v x ∂volume :=
    (windowExpGram_pairing_eq_integral a b nodes u v).symm
  have htri : ‖∫ x : ℝ in a..b,
        star (windowTaperComb nodes u x) * windowTaperComb nodes v x ∂volume‖
      ≤ ∫ x : ℝ in a..b,
          ‖windowTaperComb nodes u x‖ * ‖windowTaperComb nodes v x‖ ∂volume := by
    have htriEq : ∫ x : ℝ in a..b, ‖star (windowTaperComb nodes u x)
          * windowTaperComb nodes v x‖ ∂volume
        = ∫ x : ℝ in a..b,
            ‖windowTaperComb nodes u x‖ * ‖windowTaperComb nodes v x‖ ∂volume :=
      intervalIntegral.integral_congr fun x _ => by
        rw [norm_mul, norm_star]
    exact (intervalIntegral.norm_integral_le_integral_norm hab.le).trans htriEq.le
  have huC : ContinuousOn (fun x : ℝ => ‖windowTaperComb nodes u x‖) (Set.uIcc a b) := by
    show ContinuousOn (fun x : ℝ =>
        ‖∑ i : ι, u i * Complex.exp (star (nodes i) * (x : ℂ))‖) (Set.uIcc a b)
    refine ContinuousOn.norm ?_
    exact (continuous_finsetSum _ fun i _ => by continuity).continuousOn
  have hvC : ContinuousOn (fun x : ℝ => ‖windowTaperComb nodes v x‖) (Set.uIcc a b) := by
    show ContinuousOn (fun x : ℝ =>
        ‖∑ i : ι, v i * Complex.exp (star (nodes i) * (x : ℂ))‖) (Set.uIcc a b)
    refine ContinuousOn.norm ?_
    exact (continuous_finsetSum _ fun i _ => by continuity).continuousOn
  have hcs := intervalIntegral_cauchySchwarz hab.le huC hvC
  have hhn : 0 ≤ ∫ x : ℝ in a..b,
      ‖windowTaperComb nodes u x‖ * ‖windowTaperComb nodes v x‖ ∂volume :=
    intervalIntegral.integral_nonneg hab.le fun x _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have huu : (dotProduct (star u)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) u)).re
      = ∫ x : ℝ in a..b, ‖windowTaperComb nodes u x‖ ^ 2 ∂volume := by
    simp only [windowTaperComb]
    have hz := windowExpGram_quadratic_eq_integral a b nodes u
    rw [← hz, integral_norm_sq_re]
  have hvv : (dotProduct (star v)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re
      = ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume := by
    simp only [windowTaperComb]
    have hz := windowExpGram_quadratic_eq_integral a b nodes v
    rw [← hz, integral_norm_sq_re]
  have h1 : ‖dotProduct (star u)
        (Matrix.mulVec (windowExpGramMatrix a b nodes) v)‖ ^ 2
      ≤ (∫ x : ℝ in a..b,
            ‖windowTaperComb nodes u x‖ * ‖windowTaperComb nodes v x‖ ∂volume) ^ 2 := by
    rw [hpair]
    have hn : 0 ≤ ‖∫ x : ℝ in a..b, star (windowTaperComb nodes u x)
        * windowTaperComb nodes v x ∂volume‖ := norm_nonneg _
    nlinarith [htri, hhn, hn]
  calc ‖dotProduct (star u) (Matrix.mulVec (windowExpGramMatrix a b nodes) v)‖ ^ 2
      ≤ (∫ x : ℝ in a..b,
            ‖windowTaperComb nodes u x‖ * ‖windowTaperComb nodes v x‖ ∂volume) ^ 2 := h1
    _ ≤ (∫ x : ℝ in a..b, ‖windowTaperComb nodes u x‖ ^ 2 ∂volume)
        * ∫ x : ℝ in a..b, ‖windowTaperComb nodes v x‖ ^ 2 ∂volume := by
          simpa only [pow_two] using hcs
    _ = (dotProduct (star u)
          (Matrix.mulVec (windowExpGramMatrix a b nodes) u)).re
        * (dotProduct (star v)
            (Matrix.mulVec (windowExpGramMatrix a b nodes) v)).re := by rw [huu, hvv]

end C1WindowTaperCore
end Source
end ConnesWeilRH
