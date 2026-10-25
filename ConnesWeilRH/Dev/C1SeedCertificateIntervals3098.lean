import ConnesWeilRH.Dev.C1SeedEndpointMajorants2732
import ConnesWeilRH.Dev.C1SeedRationalPhaseBox2736

/-! Exact rational arithmetic for the finite seed certificates. Bounds are
checked as rational inequalities and transported to the existing real
interval semantics. No evaluator result is trusted as an analytic premise. -/

namespace ConnesWeilRH.Dev.C1SeedCertificate3098

open ConnesWeilRH.Source.C1ExplicitSmoothSeed

structure Box where
  lo : Rat
  hi : Rat
  deriving DecidableEq, Repr

namespace Box

def Mem (a : Box) (x : Real) : Prop := (a.lo : Real) ≤ x ∧ x ≤ a.hi
def point (x : Rat) : Box := ⟨x, x⟩
def add (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Box) : Box := ⟨a.lo - b.hi, a.hi - b.lo⟩
def mul (a b : Box) : Box :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩
def inv (a : Box) : Box := ⟨a.hi⁻¹, a.lo⁻¹⟩
def pow (a : Box) : Nat → Box
  | 0 => point 1
  | n + 1 => (pow a n).mul a
def sum (f : Nat → Box) : Nat → Box
  | 0 => point 0
  | n + 1 => (sum f n).add (f n)
def Contains (a b : Box) : Prop := a.lo ≤ b.lo ∧ b.hi ≤ a.hi
instance (a b : Box) : Decidable (a.Contains b) := inferInstanceAs
  (Decidable (a.lo ≤ b.lo ∧ b.hi ≤ a.hi))
def absUpper (a : Box) : Rat := max |a.lo| |a.hi|

theorem mem_point (x : Rat) : (point x).Mem (x : Real) := ⟨le_rfl, le_rfl⟩

theorem mem_add {a b : Box} {x y : Real} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add b).Mem (x + y) := by
  simpa only [Mem, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem mem_sub {a b : Box} {x y : Real} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub b).Mem (x - y) := by
  simpa only [Mem, sub, Rat.cast_sub] using
    And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

theorem mem_mul {a b : Box} {x y : Real} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x * y) := by
  have h := RealInterval2429.mem_mul
    (a := ⟨a.lo, a.hi⟩) (b := ⟨b.lo, b.hi⟩) hx hy
  simpa [Mem, mul, RealInterval2429.Mem, RealInterval2429.mul, Rat.cast_mul] using h

theorem mem_inv {a : Box} {x : Real} (hpos : 0 < a.lo) (hx : a.Mem x) :
    a.inv.Mem x⁻¹ := by
  have hp : (0 : Real) < a.lo := by exact_mod_cast hpos
  have h := RealInterval2429.mem_invPositive (a := ⟨a.lo, a.hi⟩) hp hx
  simpa [Mem, inv, RealInterval2429.Mem, RealInterval2429.invPositive] using h

theorem mem_pow {a : Box} {x : Real} (hx : a.Mem x) (n : Nat) :
    (a.pow n).Mem (x ^ n) := by
  induction n with
  | zero => simpa [pow] using mem_point 1
  | succ n ih => simpa [pow, pow_succ] using mem_mul ih hx

theorem mem_sum (f : Nat → Box) (v : Nat → Real) (n : Nat)
    (h : ∀ j < n, (f j).Mem (v j)) :
    (sum f n).Mem (∑ j ∈ Finset.range n, v j) := by
  induction n with
  | zero => simpa [sum] using mem_point 0
  | succ n ih =>
    rw [sum, Finset.sum_range_succ]
    exact mem_add (ih (fun j hj => h j (by omega))) (h n (by omega))

theorem mem_of_contains {a b : Box} {x : Real} (hab : a.Contains b)
    (hx : b.Mem x) : a.Mem x := by
  have hlo : (a.lo : Real) ≤ b.lo := by exact_mod_cast hab.1
  have hhi : (b.hi : Real) ≤ a.hi := by exact_mod_cast hab.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem norm_le_absUpper {a : Box} {x : Real} (hx : a.Mem x) :
    ‖x‖ ≤ (a.absUpper : Real) := by
  rw [Real.norm_eq_abs, abs_le]
  have hlo : -(a.absUpper : Real) ≤ a.lo := by
    have h : -a.absUpper ≤ a.lo :=
      (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
    exact_mod_cast h
  have hhi : (a.hi : Real) ≤ a.absUpper := by
    have h : a.hi ≤ a.absUpper := (le_abs_self _).trans (le_max_right _ _)
    exact_mod_cast h
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end Box

def cell (i : Nat) : Box :=
  ⟨(8192 + 2047 * i : Rat) / 33554432,
    (8192 + 2047 * (i + 1) : Rat) / 33554432⟩

def dyadic (lo hi : Int) : Box :=
  ⟨(lo : Rat) / (2 : Rat) ^ 256, (hi : Rat) / (2 : Rat) ^ 256⟩

def phaseBox (B : Box) (n : Nat) : Box :=
  (Box.point (n.factorial : Rat)).mul
    (((Box.point 1).sub B).inv.pow (n + 1) |>.sub
      ((Box.point ((-1 : Rat) ^ n)).mul (B.inv.pow (n + 1))))

theorem phaseBox_mem (B : Box) (n : Nat) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    {x : Real} (hx : B.Mem x) :
    (phaseBox B n).Mem (iteratedDeriv n transitionPhase2731 x) := by
  have hx0 : 0 < x := (show (0 : Real) < B.lo by exact_mod_cast hlo).trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt (by exact_mod_cast hhi)
  have href : ((Box.point 1).sub B).Mem (1 - x) := by
    simpa using Box.mem_sub (Box.mem_point 1) hx
  have hrefpos : 0 < ((Box.point 1).sub B).lo := by
    change 0 < 1 - B.hi
    linarith
  have hu := Box.mem_pow (Box.mem_inv hlo hx) (n + 1)
  have hv := Box.mem_pow (Box.mem_inv hrefpos href) (n + 1)
  have hs := Box.mem_mul (Box.mem_point ((-1 : Rat) ^ n)) hu
  have hp := Box.mem_mul (Box.mem_point (n.factorial : Rat)) (Box.mem_sub hv hs)
  rw [iteratedDeriv_transitionPhase2732 n hx0 hx1]
  convert hp using 1 <;> push_cast <;> ring

def expTaylorQ (x : Rat) : Rat := ∑ j ∈ Finset.range 20, x ^ j / (j.factorial : Rat)
def expTailQ (x : Rat) : Rat := x ^ 20 * 21 / ((20 : Nat).factorial * (20 : Rat))
def initialExp (P : Box) (k : Nat) : Box :=
  ⟨(expTaylorQ (-P.lo / (2 : Rat) ^ k) + expTailQ (-P.lo / (2 : Rat) ^ k))⁻¹,
    (expTaylorQ (-P.hi / (2 : Rat) ^ k) - expTailQ (-P.hi / (2 : Rat) ^ k))⁻¹⟩

theorem cast_expTaylorQ (x : Rat) : (expTaylorQ x : Real) = expTaylor (x : Real) := by
  simp [expTaylorQ, expTaylor]

theorem cast_expTailQ (x : Rat) : (expTailQ x : Real) = expTail (x : Real) := by
  simp [expTailQ, expTail]
  norm_num

theorem initialExp_mem (P : Box) (k : Nat) (hP : P.hi ≤ 0)
    (hcap : -P.lo ≤ (2 : Rat) ^ k) {z : Real} (hz : P.Mem z) :
    (initialExp P k).Mem (Real.exp (z / (2 : Real) ^ k)) := by
  let R : RealInterval2429 :=
    ⟨(P.lo : Real) / (2 : Real) ^ k, (P.hi : Real) / (2 : Real) ^ k⟩
  have hR : R.Mem (z / (2 : Real) ^ k) :=
    ⟨div_le_div_of_nonneg_right hz.1 (by positivity),
      div_le_div_of_nonneg_right hz.2 (by positivity)⟩
  have hRhi : R.hi ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hP) (by positivity)
  have hRcap : -R.lo ≤ (1 : Real) := by
    have hcapR : -(P.lo : Real) ≤ (2 : Real) ^ k := by exact_mod_cast hcap
    simpa [R, neg_div] using (div_le_one (by positivity : (0 : Real) < 2 ^ k)).mpr hcapR
  have h := rationalPhaseExpBox_mem2736 R 1 (by omega) hRhi (by simpa using hRcap) hR
  simpa [Box.Mem, initialExp, rationalPhaseExpBox2736, R, RealInterval2429.Mem,
    cast_expTaylorQ, cast_expTailQ, neg_div] using h

end ConnesWeilRH.Dev.C1SeedCertificate3098
