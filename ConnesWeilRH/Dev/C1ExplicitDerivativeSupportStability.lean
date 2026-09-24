import ConnesWeilRH.Dev.C1ExplicitDerivativeLadder
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeSharp

/-!
# Support stability under differentiation: one radius for the whole ladder

The order-`m` budget of the ladder asks for a support radius and a sup norm of
the `m`-th iterated derivative. The radius is not a new unknown at every order:
the support of a derivative never leaves the closure of the support of the
function, because a point outside that closure has a neighbourhood on which the
function vanishes identically and the derivative vanishes there too. So

* `support_deriv_subset_closure_support` : `support (deriv f) ⊆ closure (support f)`
  for every `f : ℝ → ℂ`;
* `support_iteratedDeriv_subset_closure_support` and `..._subset_Icc` : the same
  for every iterated derivative, and hence a single interval `[-B, B]`;
* `derivOrderL1_le_of_supportRadius` : the order-`m` support-times-sup budget
  with the support hypothesis taken at the function itself, so the radius of the
  ladder is one number for all orders;
* `derivOrderL1_smoothSeed_le` : for the committed seed the ladder bound reads
  `derivOrderL1 m smoothSeed <= 4 * M`, with `M` the only remaining input, the
  sup norm of the `m`-th derivative; the `m = 1` case reproduces the committed
  `derivativeL1 smoothSeed <= 8` of record 1969;
* `l1Mass_shiftedProduct_smoothSeed_le` : the whole seed ladder with a single
  unknown family `M : ℕ → ℝ`;
* `l1Mass_cardinalRaw_le_ladder` : the same ladder bound for the committed
  `cardinalRaw` functional, whose budget consumer it feeds.

No number is chosen for the family `M`; this file reduces the shifted-product
budget to the sup norms of the seed's iterated derivatives and nothing else.
-/

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root
open ConnesWeilRH.Source.C1ExplicitSmoothSeed

open scoped Topology

noncomputable section

/-! ## 1. The support of a derivative sits in the closure of the support -/

theorem support_deriv_subset_closure_support (f : ℝ → ℂ) :
    Function.support (deriv f) ⊆ closure (Function.support f) := by
  intro x hx
  by_contra hxc
  have hmem : (closure (Function.support f))ᶜ ∈ 𝓝 x :=
    isClosed_closure.isOpen_compl.mem_nhds hxc
  have h0 : f =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    filter_upwards [hmem] with y hy
    by_contra hne
    exact hy (subset_closure (Function.mem_support.mpr hne))
  have hz : deriv f x = 0 := by
    rw [Filter.EventuallyEq.deriv_eq h0, deriv_const]
  exact (Function.mem_support.mp hx) hz

theorem support_iteratedDeriv_subset_closure_support (j : ℕ) (f : ℝ → ℂ) :
    Function.support (iteratedDeriv j f) ⊆ closure (Function.support f) := by
  induction j with
  | zero =>
      rw [iteratedDeriv_zero]
      exact subset_closure
  | succ j ih =>
      rw [iteratedDeriv_succ]
      calc Function.support (deriv (iteratedDeriv j f))
          ⊆ closure (Function.support (iteratedDeriv j f)) :=
            support_deriv_subset_closure_support _
        _ ⊆ closure (closure (Function.support f)) := closure_mono ih
        _ = closure (Function.support f) := closure_closure

/-- One interval bounds every order: the support hypothesis is needed at the
function only. -/
theorem support_iteratedDeriv_subset_Icc (j : ℕ) {f : ℝ → ℂ} {B : ℝ}
    (h : Function.support f ⊆ Set.Icc (-B) B) :
    Function.support (iteratedDeriv j f) ⊆ Set.Icc (-B) B :=
  (support_iteratedDeriv_subset_closure_support j f).trans
    (closure_minimal h isClosed_Icc)

/-! ## 2. The order-`m` budget with the radius taken at the function -/

theorem derivOrderL1_le_of_supportRadius
    (m : ℕ) (f : CompactLogTest) (B M : ℝ)
    (hB : 0 ≤ B)
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hbound : ∀ x : ℝ, ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ ≤ M) :
    derivOrderL1 m f ≤ (2 * B) * M :=
  derivOrderL1_le_of_support_of_norm_le m f B M hB
    (support_iteratedDeriv_subset_Icc m hsupport) hbound

/-! ## 3. The seed side: one unknown family -/

/-- The function level companion of the committed
`support_deriv_smoothSeed_test_subset`; every iterated derivative of the seed
therefore has support in `[-2, 2]` by section 1. -/
theorem support_smoothSeed_test_subset :
    Function.support (smoothSeed.test : ℝ → ℂ) ⊆ Set.Icc (-2) 2 := by
  intro x hx
  refine smoothSeedComplex_support_subset ?_
  rw [Function.mem_support]
  intro hzero
  exact (Function.mem_support.mp hx) (by rw [smoothSeed_apply]; exact hzero)

/-- Sharp seed oracle: the ladder value at order `m` is at most `4 * M` whenever
`M` bounds the `m`-th derivative, the radius `2` being fixed for all orders. -/
theorem derivOrderL1_smoothSeed_le (m : ℕ) (M : ℝ)
    (hbound : ∀ x : ℝ, ‖iteratedDeriv m (smoothSeed.test : ℝ → ℂ) x‖ ≤ M) :
    derivOrderL1 m smoothSeed ≤ 4 * M := by
  have h := derivOrderL1_le_of_supportRadius m smoothSeed 2 M (by norm_num)
    support_smoothSeed_test_subset hbound
  calc derivOrderL1 m smoothSeed ≤ (2 * 2) * M := h
    _ = 4 * M := by norm_num

/-- Consistency with record 1969: the order-one oracle with the committed sup
bound `2` returns the committed `derivativeL1 smoothSeed <= 8`. -/
theorem derivOrderL1_one_smoothSeed_le_eight : derivativeL1 smoothSeed ≤ 8 := by
  have hbound : ∀ x : ℝ, ‖iteratedDeriv 1 (smoothSeed.test : ℝ → ℂ) x‖ ≤ 2 := by
    intro x
    rw [iteratedDeriv_one]
    exact norm_deriv_smoothSeed_test_le_two x
  have h := derivOrderL1_smoothSeed_le 1 2 hbound
  rw [derivOrderL1_one] at h
  calc derivativeL1 smoothSeed ≤ 4 * 2 := h
    _ = 8 := by norm_num

/-! ## 4. The ladder budget is monotone in the ladder, and the seed ladder -/

theorem ladderBound_mono {L L' : ℕ → ℝ} (h : ∀ j, L j ≤ L' j)
    (nodes : List ℂ) (m : ℕ) :
    ladderBound L nodes m ≤ ladderBound L' nodes m := by
  induction nodes generalizing m with
  | nil => simpa using h m
  | cons a as ih =>
      rw [ladderBound_cons, ladderBound_cons]
      exact add_le_add (ih (m + 1)) (mul_le_mul_of_nonneg_left (ih m) (norm_nonneg a))

/-- The seed ladder with a single unknown family `M` of sup norms of the
iterated derivatives of the committed seed. -/
theorem l1Mass_shiftedProduct_smoothSeed_le (nodes : List ℂ) (M : ℕ → ℝ)
    (hM : ∀ j x, ‖iteratedDeriv j (smoothSeed.test : ℝ → ℂ) x‖ ≤ M j) :
    l1Mass (shiftedProduct nodes smoothSeed) ≤ ladderBound (fun j => 4 * M j) nodes 0 :=
  (l1Mass_shiftedProduct_le_ladder nodes smoothSeed).trans
    (ladderBound_mono (fun j => derivOrderL1_smoothSeed_le j (M j) (hM j)) nodes 0)

/-! ## 5. The ladder reaches the committed `cardinalRaw` functional -/

/-- The committed `cardinalRaw` budget consumer accepts the ladder of the
exponentially weighted seed as its budget function, since the step condition of
that consumer is exactly the ladder recursion. -/
theorem l1Mass_cardinalRaw_le_ladder (nodes : Finset ℂ) (f : CompactLogTest) (z : ℂ) :
    l1Mass (cardinalRaw nodes f z) ≤
      ladderBound (fun j => derivOrderL1 j (exponentialWeight f (-z)))
        (nodes.erase z).toList 0 :=
  l1Mass_cardinalRaw_le_of_budget nodes f z
    (fun as => ladderBound (fun j => derivOrderL1 j (exponentialWeight f (-z))) as 0)
    (by simp [derivOrderL1_zero])
    (fun a as => by
      have h := derivOrderL1_shiftedProduct_le 1 as (exponentialWeight f (-z))
      rw [derivOrderL1_one] at h
      simp only [ladderBound_cons, Nat.zero_add]
      linarith)

end

end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
