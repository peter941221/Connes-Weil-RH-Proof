import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import Mathlib.Tactic.NormNum

namespace ConnesWeilRH.Dev

#print axioms ComplexRect2427.mem_add
#print axioms ComplexRect2427.mem_sub
#print axioms ComplexRect2427.mem_mul
#print axioms ComplexRect2427.mem_scale
#print axioms ComplexRect2427.mem_sum
#print axioms ComplexRect2427.mem_sumFinset
#print axioms RealInterval2429.mem_add
#print axioms RealInterval2429.mem_sub
#print axioms RealInterval2429.mem_mul

example : (RealInterval2429.mul ⟨-3, -1⟩ ⟨2, 4⟩).Mem (-2 * 3) := by
  apply RealInterval2429.mem_mul <;> norm_num [RealInterval2429.Mem]

example : (RealInterval2429.mul ⟨-3, 2⟩ ⟨-5, 7⟩).Mem (-2 * -4) := by
  apply RealInterval2429.mem_mul <;> norm_num [RealInterval2429.Mem]

example : (RealInterval2429.mul ⟨-3, 2⟩ ⟨0, 0⟩).Mem (1 * 0) := by
  apply RealInterval2429.mem_mul <;> norm_num [RealInterval2429.Mem]

example : (RealInterval2429.mul ⟨2, 2⟩ ⟨-4, -4⟩).Mem (2 * -4) := by
  apply RealInterval2429.mem_mul <;> norm_num [RealInterval2429.Mem]

example : (RealInterval2429.mul ⟨-3, 2⟩ ⟨-5, 7⟩).lo = -21 ∧
    (RealInterval2429.mul ⟨-3, 2⟩ ⟨-5, 7⟩).hi = 15 := by
  norm_num [RealInterval2429.mul]

example : (RealInterval2429.sub ⟨1, 2⟩ ⟨3, 5⟩).lo = -4 ∧
    (RealInterval2429.sub ⟨1, 2⟩ ⟨3, 5⟩).hi = -1 := by
  norm_num [RealInterval2429.sub]

end ConnesWeilRH.Dev
