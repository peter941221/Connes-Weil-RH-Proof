import ConnesWeilRH.Dev.C1ExplicitFiniteNodeCorrection
import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

/-!
# Derivative/L1 budgets for the explicit finite-node selector

This file records the exact one-step budget exposed by derivativeShift and
the resulting list recurrence for the actual shiftedProduct used by
cardinalRaw. It intentionally does not choose numerical derivative
constants; those constants are the next analytic obligation.
-/

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root

noncomputable section

def derivativeL1 (f : CompactLogTest) : ℝ :=
  ∫ x : ℝ, ‖deriv (f.test : ℝ → ℂ) x‖

theorem derivativeL1_nonneg (f : CompactLogTest) : 0 ≤ derivativeL1 f := by
  exact integral_nonneg fun _ => norm_nonneg _

private theorem derivative_integrand_integrable (f : CompactLogTest) :
    Integrable (fun x : ℝ => ‖deriv (f.test : ℝ → ℂ) x‖) := by
  have hderiv : ContDiff ℝ (⊤ : ℕ∞) (deriv (f.test : ℝ → ℂ)) := by
    simpa [Function.iterate_succ_apply] using
      (ContDiff.iterate_deriv 1 (f.test.smooth ⊤))
  have hcompact : HasCompactSupport (deriv (f.test : ℝ → ℂ)) :=
    f.compactSupport.deriv
  exact (hderiv.continuous.integrable_of_hasCompactSupport hcompact).norm

theorem l1Mass_derivativeShift_le (f : CompactLogTest) (a : ℂ) :
    l1Mass (derivativeShift f a) ≤ derivativeL1 f + ‖a‖ * l1Mass f := by
  have hleft : Integrable (fun x : ℝ =>
      ‖deriv (f.test : ℝ → ℂ) x + a * f.test x‖) := by
    simpa [derivativeShift_apply] using
      (derivativeShift f a).test.integrable.norm
  have hderiv : Integrable (fun x : ℝ => ‖deriv (f.test : ℝ → ℂ) x‖) :=
    derivative_integrand_integrable f
  have htest : Integrable (fun x : ℝ => ‖a‖ * ‖f.test x‖) :=
    f.test.integrable.norm.const_mul _
  have hpoint (x : ℝ) :
      ‖deriv (f.test : ℝ → ℂ) x + a * f.test x‖ ≤
        ‖deriv (f.test : ℝ → ℂ) x‖ + ‖a‖ * ‖f.test x‖ := by
    calc
      ‖deriv (f.test : ℝ → ℂ) x + a * f.test x‖ ≤
          ‖deriv (f.test : ℝ → ℂ) x‖ + ‖a * f.test x‖ := norm_add_le _ _
      _ = ‖deriv (f.test : ℝ → ℂ) x‖ + ‖a‖ * ‖f.test x‖ := by
        rw [norm_mul]
  calc
    l1Mass (derivativeShift f a) =
        ∫ x : ℝ, ‖deriv (f.test : ℝ → ℂ) x + a * f.test x‖ := by
          rfl
    _ ≤ ∫ x : ℝ, ‖deriv (f.test : ℝ → ℂ) x‖ + ‖a‖ * ‖f.test x‖ :=
      integral_mono_ae hleft (hderiv.add htest)
        (Filter.Eventually.of_forall hpoint)
    _ = derivativeL1 f + ‖a‖ * l1Mass f := by
      rw [integral_add hderiv htest, integral_const_mul]
      rfl

def shiftedProductL1Bound : List ℂ → CompactLogTest → ℝ
  | [], f => l1Mass f
  | a :: as, f => derivativeL1 (shiftedProduct as f) +
      ‖a‖ * shiftedProductL1Bound as f

theorem l1Mass_shiftedProduct_le (nodes : List ℂ) (f : CompactLogTest) :
    l1Mass (shiftedProduct nodes f) ≤ shiftedProductL1Bound nodes f := by
  induction nodes with
  | nil => rfl
  | cons a as ih =>
      simpa [shiftedProduct, shiftedProductL1Bound] using
        (l1Mass_derivativeShift_le (shiftedProduct as f) a).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left ih (norm_nonneg a)) _)

theorem l1Mass_cardinalRaw_le (nodes : Finset ℂ) (seed : CompactLogTest) (z : ℂ) :
    l1Mass (cardinalRaw nodes seed z) ≤
      shiftedProductL1Bound (nodes.erase z).toList
        (exponentialWeight seed (-z)) := by
  exact l1Mass_shiftedProduct_le _ _


theorem norm_nodeProduct_self_ge_pow
    (nodes : Finset ℂ) (z : ℂ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hsep : ∀ t ∈ nodes.erase z, delta ≤ ‖t - z‖) :
    delta ^ (nodes.erase z).card ≤ ‖nodeProduct nodes z z‖ := by
  classical
  unfold nodeProduct
  have hlist : ∀ xs : List ℂ,
      (∀ t ∈ xs, delta ≤ ‖t - z‖) →
      delta ^ xs.length ≤ ‖(xs.map (fun t => t - z)).prod‖ := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons t ts ih =>
        intro hxs
        have ht : delta ≤ ‖t - z‖ := hxs t (by simp)
        have hts : ∀ u ∈ ts, delta ≤ ‖u - z‖ := by
          intro u hu
          exact hxs u (by simp [hu])
        rw [List.length_cons, pow_succ]
        have hmul :
            delta ^ ts.length * delta ≤
              ‖(ts.map (fun u => u - z)).prod‖ * ‖t - z‖ := by
          exact mul_le_mul (ih hts) ht
            hdelta
            (norm_nonneg _)
        simpa [List.map_cons, List.prod_cons, norm_mul, mul_comm, mul_left_comm,
          mul_assoc] using hmul
  simpa only [Finset.length_toList] using
    hlist (nodes.erase z).toList (by
      intro t ht
      exact hsep t (Finset.mem_toList.mp ht))


/-- Any certified scalar recurrence can consume the exact shiftedProduct
L1 recurrence without changing the actual owner list. -/
theorem l1Mass_shiftedProduct_le_of_budget
    (nodes : List ℂ) (f : CompactLogTest) (budget : List ℂ → ℝ)
    (hbase : l1Mass f ≤ budget [])
    (hstep : ∀ a as,
      derivativeL1 (shiftedProduct as f) + ‖a‖ * budget as ≤ budget (a :: as)) :
    l1Mass (shiftedProduct nodes f) ≤ budget nodes := by
  induction nodes with
  | nil => exact hbase
  | cons a as ih =>
      calc
        l1Mass (shiftedProduct (a :: as) f) ≤
            derivativeL1 (shiftedProduct as f) +
              ‖a‖ * l1Mass (shiftedProduct as f) := by
                simpa [shiftedProduct] using
                  l1Mass_derivativeShift_le (shiftedProduct as f) a
        _ ≤ derivativeL1 (shiftedProduct as f) + ‖a‖ * budget as :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih (norm_nonneg a)) _
        _ ≤ budget (a :: as) := hstep a as

theorem l1Mass_cardinalRaw_le_of_budget
    (nodes : Finset ℂ) (seed : CompactLogTest) (z : ℂ)
    (budget : List ℂ → ℝ)
    (hbase : l1Mass (exponentialWeight seed (-z)) ≤ budget [])
    (hstep : ∀ a as,
      derivativeL1
        (shiftedProduct as (exponentialWeight seed (-z))) +
        ‖a‖ * budget as ≤ budget (a :: as)) :
    l1Mass (cardinalRaw nodes seed z) ≤ budget (nodes.erase z).toList := by
  exact l1Mass_shiftedProduct_le_of_budget
    (nodes.erase z).toList (exponentialWeight seed (-z)) budget hbase hstep


theorem derivativeL1_le_of_support_of_norm_le
    (f : CompactLogTest) (B M : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hsupport : Function.support (deriv (f.test : ℝ → ℂ)) ⊆ Set.Icc (-B) B)
    (hbound : ∀ x : ℝ, ‖deriv (f.test : ℝ → ℂ) x‖ ≤ M) :
    derivativeL1 f ≤ (2 * B) * M := by
  have hleft : Integrable (fun x : ℝ => ‖deriv (f.test : ℝ → ℂ) x‖) :=
    derivative_integrand_integrable f
  let bound : ℝ → ℝ := Set.indicator (Set.Icc (-B) B) (fun _ => M)
  have hright : Integrable bound := by
    exact (integrableOn_const (μ := volume) (C := M)
      (by rw [Real.volume_Icc]; simp [hB]) (by simp [hM])).integrable_indicator
      measurableSet_Icc
  have hpoint : ∀ x : ℝ, ‖deriv (f.test : ℝ → ℂ) x‖ ≤ bound x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-B) B
    · simp only [bound, Set.indicator_of_mem hx]
      exact hbound x
    · simp only [bound, Set.indicator, hx, ↓reduceIte]
      have hzero : deriv (f.test : ℝ → ℂ) x = 0 := by
        by_contra hne
        exact hx (hsupport (Function.mem_support.mpr hne))
      simp [hzero]
  calc
    derivativeL1 f ≤ ∫ x : ℝ, bound x :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = (2 * B) * M := by
      rw [show bound = Set.indicator (Set.Icc (-B) B) (fun _ => M) by rfl]
      rw [integral_indicator measurableSet_Icc]
      simp [Real.volume_Icc, max_eq_left (by linarith : 0 ≤ B + B)]
      exact Or.inl (by ring)

end
end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
