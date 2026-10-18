import ConnesWeilRH.Dev.C1RouteBNodeProductEnvelope2821
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_finite_node_product_envelope2822
    {ι : Type} {s : Finset ι} (a A : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ A i) :
    |Finset.prod s a| ≤ Finset.prod s A := by
  have hp := Finset.prod_induction
    (s := s) (f := fun i => (a i, A i))
    (p := fun z : ℝ × ℝ => |z.1| ≤ z.2)
    (fun x y hx hy => by
      have hx0 : 0 ≤ x.2 := le_trans (abs_nonneg x.1) hx
      simpa [abs_mul] using mul_le_mul hx hy (abs_nonneg y.1) hx0)
    (by simp)
    (by intro i hi; exact ha i hi)
  have hfst := map_prod (MonoidHom.fst ℝ ℝ) (fun i => (a i, A i)) s
  have hsnd := map_prod (MonoidHom.snd ℝ ℝ) (fun i => (a i, A i)) s
  change (Finset.prod s (fun i => (a i, A i))).1 = Finset.prod s a at hfst
  change (Finset.prod s (fun i => (a i, A i))).2 = Finset.prod s A at hsnd
  have hfst' := hfst
  have hsnd' := hsnd
  change |(Finset.prod s (fun i => (a i, A i))).1| ≤
    (Finset.prod s (fun i => (a i, A i))).2 at hp
  rw [hfst', hsnd'] at hp
  simpa using hp

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
