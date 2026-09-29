import Mathlib.Analysis.Complex.Trigonometric

/-!
# Route-A exponential perturbation brick

This is the analytic propagation step behind the AMP allowance used by the
vector-aware direct-product price.  It is independent of the numerical owner:
the owner-specific work only has to supply a bound on `‖δ‖`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAExpPerturbation

theorem norm_exp_add_sub_exp_le {z δ : ℂ} (hδ : ‖δ‖ ≤ 1) :
    ‖Complex.exp (z + δ) - Complex.exp z‖ ≤
      2 * Real.exp z.re * ‖δ‖ := by
  calc
    ‖Complex.exp (z + δ) - Complex.exp z‖ =
        ‖Complex.exp z * (Complex.exp δ - 1)‖ := by
      rw [Complex.exp_add]
      ring_nf
    _ = ‖Complex.exp z‖ * ‖Complex.exp δ - 1‖ := Complex.norm_mul _ _
    _ = Real.exp z.re * ‖Complex.exp δ - 1‖ := by
      rw [Complex.norm_exp]
    _ ≤ Real.exp z.re * (2 * ‖δ‖) := by
      exact mul_le_mul_of_nonneg_left
        (Complex.norm_exp_sub_one_le hδ) (le_of_lt (Real.exp_pos _))
    _ = 2 * Real.exp z.re * ‖δ‖ := by ring

theorem norm_mul_exp_add_sub_exp_le {c z δ : ℂ} (hδ : ‖δ‖ ≤ 1) :
    ‖c * (Complex.exp (z + δ) - Complex.exp z)‖ ≤
      2 * ‖c‖ * Real.exp z.re * ‖δ‖ := by
  calc
    ‖c * (Complex.exp (z + δ) - Complex.exp z)‖ =
        ‖c‖ * ‖Complex.exp (z + δ) - Complex.exp z‖ :=
      Complex.norm_mul _ _
    _ ≤ ‖c‖ * (2 * Real.exp z.re * ‖δ‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_exp_add_sub_exp_le hδ) (norm_nonneg c)
    _ = 2 * ‖c‖ * Real.exp z.re * ‖δ‖ := by ring

theorem norm_sum_mul_exp_add_sub_exp_le {ι : Type*} (s : Finset ι)
    (c z δ : ι → ℂ) (hδ : ∀ i ∈ s, ‖δ i‖ ≤ 1) :
    ‖s.sum (fun i => c i * (Complex.exp (z i + δ i) - Complex.exp (z i)))‖ ≤
      s.sum (fun i => 2 * ‖c i‖ * Real.exp (z i).re * ‖δ i‖) := by
  calc
    ‖s.sum (fun i => c i * (Complex.exp (z i + δ i) - Complex.exp (z i)))‖ ≤
        s.sum (fun i => ‖c i * (Complex.exp (z i + δ i) - Complex.exp (z i))‖) :=
      norm_sum_le _ _
    _ ≤ s.sum (fun i => 2 * ‖c i‖ * Real.exp (z i).re * ‖δ i‖) := by
      exact Finset.sum_le_sum fun i hi =>
        norm_mul_exp_add_sub_exp_le (hδ i hi)

theorem norm_add_sum_approx_sub_le {ι : Type*} (s : Finset ι)
    (x y E : ι → ℂ) (r : ℂ)
    (hE : ∀ i ∈ s, ‖y i - x i‖ ≤ ‖E i‖) :
    ‖r + (s.sum y - s.sum x)‖ ≤
      ‖r‖ + s.sum (fun i => ‖E i‖) := by
  have hsum : s.sum y - s.sum x = s.sum (fun i => y i - x i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  calc
    ‖r + s.sum (fun i => y i - x i)‖ ≤
        ‖r‖ + ‖s.sum (fun i => y i - x i)‖ := norm_add_le _ _
    _ ≤ ‖r‖ + s.sum (fun i => ‖y i - x i‖) := by
      have hnorm :
          ‖s.sum (fun i => y i - x i)‖ ≤
            s.sum (fun i => ‖y i - x i‖) := norm_sum_le s _
      simpa [add_comm] using add_le_add_right hnorm ‖r‖
    _ ≤ ‖r‖ + s.sum (fun i => ‖E i‖) := by
      have hsum :
          s.sum (fun i => ‖y i - x i‖) ≤
            s.sum (fun i => ‖E i‖) :=
        Finset.sum_le_sum fun i hi => hE i hi
      simpa [add_comm] using add_le_add_right hsum ‖r‖

theorem norm_add_sum_mul_exp_add_sub_exp_le {ι : Type*} (s : Finset ι)
    (c z δ : ι → ℂ) (r : ℂ)
    (hδ : ∀ i ∈ s, ‖δ i‖ ≤ 1) :
    ‖r + s.sum (fun i => c i *
        (Complex.exp (z i + δ i) - Complex.exp (z i)))‖ ≤
      ‖r‖ + s.sum (fun i =>
        2 * ‖c i‖ * Real.exp (z i).re * ‖δ i‖) := by
  calc
    ‖r + s.sum (fun i => c i *
        (Complex.exp (z i + δ i) - Complex.exp (z i)))‖ ≤
        ‖r‖ + s.sum (fun i => ‖c i *
          (Complex.exp (z i + δ i) - Complex.exp (z i))‖) := by
      have hnorm :
          ‖s.sum (fun i => c i *
            (Complex.exp (z i + δ i) - Complex.exp (z i)))‖ ≤
            s.sum (fun i => ‖c i *
              (Complex.exp (z i + δ i) - Complex.exp (z i))‖) :=
        norm_sum_le s _
      exact (norm_add_le r _).trans
        (by simpa [add_comm] using add_le_add_left hnorm ‖r‖)
    _ ≤ ‖r‖ + s.sum (fun i =>
        2 * ‖c i‖ * Real.exp (z i).re * ‖δ i‖) := by
      have hsum := Finset.sum_le_sum fun i hi =>
        norm_mul_exp_add_sub_exp_le (c := c i) (z := z i) (δ := δ i)
          (hδ i hi)
      simpa [add_comm] using add_le_add_left hsum ‖r‖

end C1RouteAExpPerturbation
end Source
end ConnesWeilRH
