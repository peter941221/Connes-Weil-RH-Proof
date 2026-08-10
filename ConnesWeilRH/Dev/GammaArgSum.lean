import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Gamma-argument sum backbone (docs/941)

`arg_prod_coe_angle`: the principal argument of a finite product of non-zero
complex numbers equals the sum of their arguments, as `Real.Angle`.  This is
the structural additivity that turns the Weierstrass log-Gamma factor arguments
(see `GammaArgBricks.arg_one_add_I_*`) into the summed series at the finite-S
base point `1 + I/2`.

All lemmas are axiom-clean off mathlib foundations (`[propext,
Classical.choice, Quot.sound]`, 0 sorry). RH NOT claimed.
-/
open Complex

namespace ConnesWeilRH
namespace Dev
namespace GammaArgSum

/-- Argument of a `Finset` product (as `Real.Angle`) = sum of the arguments,
stated for an arbitrary index type so the Weierstrass factor product can be
indexed over real scales. -/
theorem arg_prod_coe_angle {α : Type*} (t : Finset α) (f : α → ℂ)
    (hfs : ∀ i ∈ t, f i ≠ 0) :
    ((Finset.prod t f).arg : Real.Angle) = Finset.sum t (fun i => (f i).arg) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.sum_insert has]
      have hf : f a ≠ 0 := hfs a (Finset.mem_insert_self a s)
      have hprod : Finset.prod s f ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        exact hfs i (Finset.mem_insert_of_mem hi)
      rw [arg_mul_coe_angle hf hprod]
      have hfs' : ∀ i ∈ s, f i ≠ 0 := fun i hi => hfs i (Finset.mem_insert_of_mem hi)
      rw [ih hfs']
      rfl

/-- The real-to-`Real.Angle` coercion distributes over a finite sum. -/
lemma real_sum_coe_angle {α : Type*} (t : Finset α) (r : α → ℝ) :
    ((Finset.sum t r : Real) : Real.Angle) = Finset.sum t (fun i => (r i : Real.Angle)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      rw [Real.Angle.coe_add]
      rw [ih]

end GammaArgSum
end Dev
end ConnesWeilRH
