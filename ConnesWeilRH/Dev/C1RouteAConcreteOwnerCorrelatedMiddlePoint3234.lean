import ConnesWeilRH.Dev.C1RouteAConcreteOwnerMiddlePointRect3232
import ConnesWeilRH.Dev.C1RouteACorrelatedBall3233

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680MiddlePointFamilyBall3234
    (family : Fin 30) : ComplexNormBall3233 :=
  ComplexNormBall3233.ofRect (record2680MiddlePointFamilyRect3232 family)

theorem record2680_middle_point_family_ball_mem3234
    {family : Fin 30}
    (hre : (record2680MiddlePointFamilyRect3232 family).reLo ≤
      (record2680MiddlePointFamilyRect3232 family).reHi)
    (him : (record2680MiddlePointFamilyRect3232 family).imLo ≤
      (record2680MiddlePointFamilyRect3232 family).imHi) :
    (record2680MiddlePointFamilyBall3234 family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 17168)) := by
  unfold record2680MiddlePointFamilyBall3234
  exact ComplexNormBall3233.mem_ofRect hre him
    (record2680_middle_point_family_mem3232 (family := family))

noncomputable def record2680MiddlePointAggregateBall3234 :
    ComplexNormBall3233 :=
  ComplexNormBall3233.sumFinset record2680MiddlePointFamilyBall3234 Finset.univ

theorem realInterval2429_add_order
    {a b : RealInterval2429}
    (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    (a.add b).lo ≤ (a.add b).hi := by
  dsimp [RealInterval2429.add]
  exact add_le_add ha hb

theorem realInterval2429_sub_order
    {a b : RealInterval2429}
    (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    (a.sub b).lo ≤ (a.sub b).hi := by
  dsimp [RealInterval2429.sub]
  linarith

theorem realInterval2429_mul_order
    {a b : RealInterval2429} :
    (a.mul b).lo ≤ (a.mul b).hi := by
  dsimp [RealInterval2429.mul]
  calc
    min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi)) ≤ a.lo * b.lo := by
          exact (min_le_left _ _).trans (min_le_left _ _)
    _ ≤ max (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi)) := by
          exact le_max_of_le_left (le_max_left _ _)

theorem complexRect2427_mul_order
    {a b : ComplexRect2427} :
    (a.mul b).reLo ≤ (a.mul b).reHi ∧
      (a.mul b).imLo ≤ (a.mul b).imHi := by
  let ar : RealInterval2429 := ⟨a.reLo, a.reHi⟩
  let ai : RealInterval2429 := ⟨a.imLo, a.imHi⟩
  let br : RealInterval2429 := ⟨b.reLo, b.reHi⟩
  let bi : RealInterval2429 := ⟨b.imLo, b.imHi⟩
  have hrr := realInterval2429_mul_order (a := ar) (b := br)
  have hii := realInterval2429_mul_order (a := ai) (b := bi)
  have hri := realInterval2429_mul_order (a := ar) (b := bi)
  have hir := realInterval2429_mul_order (a := ai) (b := br)
  have hre := realInterval2429_sub_order hrr hii
  have him := realInterval2429_add_order hri hir
  exact ⟨by simpa [ComplexRect2427.mul, ar, ai, br, bi] using hre,
    by simpa [ComplexRect2427.mul, ar, ai, br, bi] using him⟩

theorem complexRect2427_point_order (z : ℂ) :
    (ComplexRect2427.point z).reLo ≤ (ComplexRect2427.point z).reHi ∧
      (ComplexRect2427.point z).imLo ≤ (ComplexRect2427.point z).imHi := by
  simp [ComplexRect2427.point]

theorem complexRectPowSq3218_order
    {rect : ComplexRect2427}
    (hrect : rect.reLo ≤ rect.reHi ∧ rect.imLo ≤ rect.imHi) :
    ∀ n, (complexRectPowSq3218 rect n).reLo ≤
        (complexRectPowSq3218 rect n).reHi ∧
      (complexRectPowSq3218 rect n).imLo ≤
        (complexRectPowSq3218 rect n).imHi := by
  intro n
  induction n with
  | zero => exact hrect
  | succ n ih =>
      exact complexRect2427_mul_order

theorem phaseRect3218_order (angle : ℝ) :
    (phaseRect3218 angle).reLo ≤ (phaseRect3218 angle).reHi ∧
      (phaseRect3218 angle).imLo ≤ (phaseRect3218 angle).imHi := by
  have herror : 0 ≤ phaseTaylorError3218 angle := by
    dsimp [phaseTaylorError3218]
    positivity
  constructor <;> dsimp [phaseRect3218] <;> linarith

theorem record2680MiddlePointBumpRect3232_order (family : Fin 30) :
    (record2680MiddlePointBumpRect3232 family).reLo ≤
        (record2680MiddlePointBumpRect3232 family).reHi ∧
      (record2680MiddlePointBumpRect3232 family).imLo ≤
        (record2680MiddlePointBumpRect3232 family).imHi := by
  have h := record2680_middle_point_bump_mem3231 (family := family)
  exact ⟨h.1.trans h.2, le_rfl⟩

theorem record2680MiddlePointFamilyRect3232_order (family : Fin 30) :
    (record2680MiddlePointFamilyRect3232 family).reLo ≤
        (record2680MiddlePointFamilyRect3232 family).reHi ∧
      (record2680MiddlePointFamilyRect3232 family).imLo ≤
        (record2680MiddlePointFamilyRect3232 family).imHi := by
  exact complexRect2427_mul_order

theorem record2680_middle_point_aggregate_ball_mem3234
    (horder : ∀ family : Fin 30,
      (record2680MiddlePointFamilyRect3232 family).reLo ≤
        (record2680MiddlePointFamilyRect3232 family).reHi ∧
      (record2680MiddlePointFamilyRect3232 family).imLo ≤
        (record2680MiddlePointFamilyRect3232 family).imHi) :
    record2680MiddlePointAggregateBall3234.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)) := by
  unfold record2680MiddlePointAggregateBall3234
  apply ComplexNormBall3233.mem_sumFinset
  intro family hfamily
  have h := horder family
  exact record2680_middle_point_family_ball_mem3234 h.1 h.2

theorem record2680_middle_point_aggregate_ball_mem_of_order3234 :
    record2680MiddlePointAggregateBall3234.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)) := by
  apply record2680_middle_point_aggregate_ball_mem3234
  exact record2680MiddlePointFamilyRect3232_order

end ConnesWeilRH.Dev
