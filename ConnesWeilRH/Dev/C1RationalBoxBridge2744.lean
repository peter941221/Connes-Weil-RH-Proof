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

def RationalBox2744.sub (a b : RationalBox2744) : RationalBox2744 :=
  { lo := a.lo - b.hi
    hi := a.hi - b.lo
    ordered := by linarith [a.ordered, b.ordered] }

theorem RationalBox2744.mem_sub {a b : RationalBox2744} {x y : ℝ}
    (hx : a.Mem x) (hy : b.Mem y) :
    (RationalBox2744.sub a b).Mem (x - y) := by
  simp only [RationalBox2744.Mem, RationalBox2744.sub]
  norm_num only [Rat.cast_sub]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem RationalBox2744.toRealInterval_add (a b : RationalBox2744) :
    (a.add b).toRealInterval =
      a.toRealInterval.add b.toRealInterval := by
  cases a
  cases b
  simp [RationalBox2744.add, RationalBox2744.toRealInterval,
    RealInterval2429.add, Rat.cast_add]

theorem RationalBox2744.toRealInterval_sub (a b : RationalBox2744) :
    (a.sub b).toRealInterval =
      a.toRealInterval.sub b.toRealInterval := by
  cases a
  cases b
  simp [RationalBox2744.sub, RationalBox2744.toRealInterval,
    RealInterval2429.sub, Rat.cast_sub]

def RationalBox2744.nsmul (c : ℚ) (hc : 0 ≤ c) (a : RationalBox2744) : RationalBox2744 :=
  { lo := c * a.lo
    hi := c * a.hi
    ordered := by exact mul_le_mul_of_nonneg_left a.ordered hc }

theorem RationalBox2744.mem_nsmul {c : ℚ} {a : RationalBox2744} {x : ℝ}
    (hc : 0 ≤ c) (hx : a.Mem x) :
    (RationalBox2744.nsmul c hc a).Mem ((c : ℝ) * x) := by
  simp only [RationalBox2744.Mem, RationalBox2744.nsmul]
  norm_num only [Rat.cast_mul]
  have hcR : (0 : ℝ) ≤ c := by exact_mod_cast hc
  constructor <;> nlinarith [hx.1, hx.2]

end ConnesWeilRH.Dev
