import ConnesWeilRH.Dev.C1RouteAOwnerWeightedIntervalIntegrable3206
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

structure RatInterval3276 where
  lo : ℚ
  hi : ℚ

namespace RatInterval3276

def toReal (a : RatInterval3276) : RealInterval2429 :=
  { lo := a.lo
    hi := a.hi }

def add (a b : RatInterval3276) : RatInterval3276 :=
  { lo := a.lo + b.lo
    hi := a.hi + b.hi }

def sub (a b : RatInterval3276) : RatInterval3276 :=
  { lo := a.lo - b.hi
    hi := a.hi - b.lo }

def mul (a b : RatInterval3276) : RatInterval3276 :=
  { lo := min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))
    hi := max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)) }

theorem toReal_add (a b : RatInterval3276) :
    (add a b).toReal = a.toReal.add b.toReal := by
  cases a
  cases b
  simp [add, toReal, RealInterval2429.add, Rat.cast_add]

theorem toReal_sub (a b : RatInterval3276) :
    (sub a b).toReal = a.toReal.sub b.toReal := by
  cases a
  cases b
  simp [sub, toReal, RealInterval2429.sub, Rat.cast_sub]

theorem toReal_mul (a b : RatInterval3276) :
    (mul a b).toReal = a.toReal.mul b.toReal := by
  cases a
  cases b
  simp [mul, toReal, RealInterval2429.mul, Rat.cast_min, Rat.cast_max,
    Rat.cast_mul]

def Mem (x : ℝ) (a : RatInterval3276) : Prop :=
  a.toReal.Mem x

theorem mem_add {a b : RatInterval3276} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (add a b).Mem (x + y) := by
  change (add a b).toReal.Mem (x + y)
  change a.toReal.Mem x at ha
  change b.toReal.Mem y at hb
  rw [show (add a b).toReal = a.toReal.add b.toReal from toReal_add a b]
  exact RealInterval2429.mem_add ha hb

theorem mem_mul {a b : RatInterval3276} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (mul a b).Mem (x * y) := by
  change (mul a b).toReal.Mem (x * y)
  change a.toReal.Mem x at ha
  change b.toReal.Mem y at hb
  rw [show (mul a b).toReal = a.toReal.mul b.toReal from toReal_mul a b]
  exact RealInterval2429.mem_mul ha hb

end RatInterval3276

structure RatRect3276 where
  reLo : ℚ
  reHi : ℚ
  imLo : ℚ
  imHi : ℚ

namespace RatRect3276

def toReal (a : RatRect3276) : ComplexRect2427 :=
  { reLo := a.reLo
    reHi := a.reHi
    imLo := a.imLo
    imHi := a.imHi }

def add (a b : RatRect3276) : RatRect3276 :=
  { reLo := a.reLo + b.reLo
    reHi := a.reHi + b.reHi
    imLo := a.imLo + b.imLo
    imHi := a.imHi + b.imHi }

def mul (a b : RatRect3276) : RatRect3276 :=
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let ai : RatInterval3276 := ⟨a.imLo, a.imHi⟩
  let br : RatInterval3276 := ⟨b.reLo, b.reHi⟩
  let bi : RatInterval3276 := ⟨b.imLo, b.imHi⟩
  let realPart := ar.mul br |>.sub (ai.mul bi)
  let imagPart := (ar.mul bi).add (ai.mul br)
  { reLo := realPart.lo
    reHi := realPart.hi
    imLo := imagPart.lo
    imHi := imagPart.hi }

def Mem (z : ℂ) (a : RatRect3276) : Prop :=
  a.toReal.Mem z

def sumFinset {α : Type*} (rect : α → RatRect3276)
    (s : Finset α) : RatRect3276 :=
  { reLo := ∑ i ∈ s, (rect i).reLo
    reHi := ∑ i ∈ s, (rect i).reHi
    imLo := ∑ i ∈ s, (rect i).imLo
    imHi := ∑ i ∈ s, (rect i).imHi }

theorem toReal_add (a b : RatRect3276) :
    (add a b).toReal = a.toReal.add b.toReal := by
  cases a
  cases b
  simp [add, toReal, ComplexRect2427.add, Rat.cast_add]

set_option maxHeartbeats 10000000 in
theorem toReal_mul (a b : RatRect3276) :
    (mul a b).toReal = a.toReal.mul b.toReal := by
  cases a
  cases b
  dsimp [mul, toReal, ComplexRect2427.mul]
  apply ComplexRect2427.ext <;>
    simp [mul, toReal, ComplexRect2427.mul, RatInterval3276.mul,
      RatInterval3276.add, RatInterval3276.sub, RatInterval3276.toReal,
      RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
      Rat.cast_add, Rat.cast_sub, Rat.cast_min, Rat.cast_max, Rat.cast_mul]

theorem toReal_sumFinset {α : Type*} (rect : α → RatRect3276)
    (s : Finset α) :
    (sumFinset rect s).toReal =
      ComplexRect2427.sumFinset (fun i => (rect i).toReal) s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [sumFinset, ComplexRect2427.sumFinset, toReal]
  | @insert a s ha ih =>
      simp [sumFinset, ComplexRect2427.sumFinset, toReal, ih,
        Rat.cast_add, Finset.sum_insert, ha]

theorem mem_sumFinset {α : Type*} {term : α → ℂ}
    {rect : α → RatRect3276} {s : Finset α}
    (hterm : ∀ i ∈ s, (rect i).Mem (term i)) :
    (sumFinset rect s).Mem (∑ i ∈ s, term i) := by
  change (sumFinset rect s).toReal.Mem (∑ i ∈ s, term i)
  rw [toReal_sumFinset]
  apply ComplexRect2427.mem_sumFinset
  intro i hi
  exact hterm i hi

theorem externalPhysical_mem_of_rat_family_rects3276
    {x : ℝ} {rect : Fin 30 → RatRect3276}
    (hrect : ∀ family,
      (rect family).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2) x)) :
    (RatRect3276.sumFinset rect Finset.univ).Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x) := by
  simpa [externalPhysical2344] using
    (RatRect3276.mem_sumFinset
      (s := (Finset.univ : Finset (Fin 30)))
      (rect := rect)
      (term := fun family => externalFamilyValue2344
        (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2) x)
      (by intro family _; exact hrect family))

theorem mem_add {a b : RatRect3276} {z w : ℂ}
    (ha : a.Mem z) (hb : b.Mem w) : (add a b).Mem (z + w) := by
  change (add a b).toReal.Mem (z + w)
  change a.toReal.Mem z at ha
  change b.toReal.Mem w at hb
  rw [show (add a b).toReal = a.toReal.add b.toReal from toReal_add a b]
  exact ComplexRect2427.mem_add ha hb

theorem mem_mul {a b : RatRect3276} {z w : ℂ}
    (ha : a.Mem z) (hb : b.Mem w) : (mul a b).Mem (z * w) := by
  change (mul a b).toReal.Mem (z * w)
  change a.toReal.Mem z at ha
  change b.toReal.Mem w at hb
  rw [show (mul a b).toReal = a.toReal.mul b.toReal from toReal_mul a b]
  exact ComplexRect2427.mem_mul ha hb

end RatRect3276

theorem weightedExternal_le_rat_rect_reHi3276
    {sigma x : ℝ} {weight : RatInterval3276} {aggregate : RatRect3276}
    (hweight : weight.Mem (Real.exp (sigma * x)))
    (haggregate : aggregate.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x)) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
        capturedModulations2584 x ≤
      (RatRect3276.mul
        { reLo := weight.lo, reHi := weight.hi, imLo := 0, imHi := 0 }
        aggregate).toReal.reHi := by
  have hweight' : RatRect3276.Mem
      ((Real.exp (sigma * x) : ℝ) : ℂ)
      ({ reLo := weight.lo, reHi := weight.hi, imLo := 0, imHi := 0 } : RatRect3276) := by
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem
    dsimp
    constructor
    · exact hweight.1
    constructor
    · exact hweight.2
    constructor <;> norm_num
  have hmul := RatRect3276.mem_mul
    (a := { reLo := weight.lo, reHi := weight.hi, imLo := 0, imHi := 0 })
    (b := aggregate) hweight' haggregate
  unfold RatRect3276.Mem at hmul
  change (RatRect3276.mul
      { reLo := weight.lo, reHi := weight.hi, imLo := 0, imHi := 0 }
      aggregate).toReal.Mem
    (((Real.exp (sigma * x) : ℝ) : ℂ) *
      externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x) at hmul
  have hupper := hmul.2.1
  unfold weightedExternal3201
  simpa only [weightedFunction2348, weightedExp2348, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_mul,
    sub_zero] using hupper

theorem weightedExternal_le_rat_family_rect_reHi3276
    {sigma x : ℝ} {weight : RatInterval3276}
    {rect : Fin 30 → RatRect3276}
    (hweight : weight.Mem (Real.exp (sigma * x)))
    (hrect : ∀ family,
      (rect family).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2) x)) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
        capturedModulations2584 x ≤
      (RatRect3276.mul
        { reLo := weight.lo, reHi := weight.hi, imLo := 0, imHi := 0 }
        (RatRect3276.sumFinset rect Finset.univ)).toReal.reHi := by
  apply weightedExternal_le_rat_rect_reHi3276 hweight
  exact RatRect3276.externalPhysical_mem_of_rat_family_rects3276 hrect

end ConnesWeilRH.Dev
