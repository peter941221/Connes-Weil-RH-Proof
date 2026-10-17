import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

structure RationalBox2744 where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

def RationalBox2744.toRealInterval (b : RationalBox2744) : RealInterval2429 :=
  { lo := b.lo
    hi := b.hi }

def RationalBox2744.Mem (x : ℝ) (b : RationalBox2744) : Prop :=
  (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

theorem RationalBox2744.mem_toRealInterval {b : RationalBox2744} {x : ℝ}
    (hx : b.Mem x) : b.toRealInterval.Mem x := by
  exact hx

theorem RationalBox2744.toRealInterval_ordered (b : RationalBox2744) :
    b.toRealInterval.lo ≤ b.toRealInterval.hi := by
  change (b.lo : ℝ) ≤ b.hi
  exact_mod_cast b.ordered

def RationalBox2744.add (a b : RationalBox2744) : RationalBox2744 :=
  { lo := a.lo + b.lo
    hi := a.hi + b.hi
    ordered := add_le_add a.ordered b.ordered }

theorem RationalBox2744.mem_add {a b : RationalBox2744} {x y : ℝ}
    (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  simp only [RationalBox2744.Mem, RationalBox2744.add]
  norm_num only [Rat.cast_add]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

end ConnesWeilRH.Dev
