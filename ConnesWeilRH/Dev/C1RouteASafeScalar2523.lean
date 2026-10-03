import ConnesWeilRH.Dev.C1RouteAFallbackCertificate2522

/-! The exact safe-cell scalar expression and rational-certificate doors.
The grid is the actual Lean stripRadius2303, not the capture's largest radius.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope

noncomputable def safeFactor2523 (c m r t : ℝ) : ℝ :=
  c * ((60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / r ^ 2) +
    (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / r) ^ 2 + m ^ 2 +
    2 * |m| * (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / r) +
    (60 * t * (1 - t ^ 2)⁻¹ ^ 2 / r + |m|) + 1 / 4)

noncomputable def safeFamily2523 (index : ℕ) (i : Fin 30) : ℝ :=
  Real.exp (ownerRad_2463 i / 2) *
    (ownerProductionExpUpper2514 index i *
      safeFactor2523 (|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)
        (ownerMod_2463 i) (ownerRad_2463 i) (ownerProductionT2516 index i))

theorem safeFactor_nonneg2523 (c m r t : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (ht : 0 ≤ t) (ht1 : t < 1) : 0 ≤ safeFactor2523 c m r t := by
  have hd : 0 ≤ 1 - t ^ 2 := by nlinarith
  unfold safeFactor2523
  positivity

theorem safeFactor_owner_nonneg2523 (index : ℕ) (i : Fin 30)
    (hlo : 196 ≤ index) (hhi : index ≤ 443) :
    0 ≤ safeFactor2523 (|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)
      (ownerMod_2463 i) (ownerRad_2463 i) (ownerProductionT2516 index i) := by
  apply safeFactor_nonneg2523 _ _ _ _ (by positivity) (ownerRadPos_2465 i)
  · exact ownerCellEndpointRatio_nonneg2488 _ _ _ _
  · have hs := (ownerCellSafeEndpoint_true_iff2488 stripRadius2303
      (stripRadius2303 / 320) index).mp
      (ownerCellSafeEndpoint_production2488 hlo hhi)
    exact ownerCellEndpointRatio_lt_one2488 _ _ _ i (hs i).1 (hs i).2

theorem production_safe_scalar2523 (sigma : ℝ) (index : ℕ)
    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ))
    (hlo : 196 ≤ index) (hhi : index ≤ 443) :
    ownerProductionRemainderTerm2521 sigma index = ∑ i : Fin 30, safeFamily2523 index i := by
  simp only [ownerProductionRemainderTerm2521, ownerProductionSafe2516,
    if_pos (And.intro hlo hhi), ↓reduceIte, ownerExpUpperCurvatureSum2515]
  apply Finset.sum_congr rfl
  intro i _
  rcases hsigma with rfl | rfl <;>
    norm_num [weightedCurvature2348, safeFamily2523, safeFactor2523,
      ownerProductionCoefficientBound2516, ownerProductionUpper2516] <;> ring

theorem exp_weight_rational2523 (r W : ℝ) (hr0 : 0 ≤ r) (hr10 : r ≤ 10)
    (hcheck : ((∑ k ∈ Finset.range 20, (r / 10) ^ k / (k.factorial : ℝ)) +
      (r / 10) ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20))) ^ 5 ≤ W) :
    Real.exp (r / 2) ≤ W := by
  have hx : |r / 10| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have he := Real.exp_bound (x := r / 10) hx (n := 20) (by norm_num)
  rw [abs_of_nonneg (by positivity : 0 ≤ r / 10)] at he
  have hupper := (abs_le.mp he).2
  have hu : Real.exp (r / 10) ≤
      (∑ k ∈ Finset.range 20, (r / 10) ^ k / (k.factorial : ℝ)) +
        (r / 10) ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20)) := by
    norm_num at hupper ⊢
    linarith
  calc
    Real.exp (r / 2) = Real.exp (r / 10) ^ 5 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hu 5
    _ ≤ W := hcheck

theorem split_upper_rational2523 (z P U : ℝ) (n : ℕ)
    (hfloor : ⌊z⌋₊ = n) (hpow : expNegOneUpper2498 ^ n ≤ P)
    (hr0 : 0 ≤ z - n) (hr1 : z - n ≤ 1)
    (hcheck : P * (expTaylor20 (z - n) + expTaylor20Error) ≤ U) :
    expNegOneUpper2498 ^ ⌊z⌋₊ *
      (expTaylor20 (z - (⌊z⌋₊ : ℕ)) + expTaylor20Error) ≤ U := by
  rw [hfloor]
  have hpoly : 0 ≤ expTaylor20 (z - n) + expTaylor20Error := by
    have h := (abs_le.mp (expTaylor20_error (z - n) hr0 hr1)).2
    linarith [Real.exp_pos (-(z - n))]
  exact (mul_le_mul_of_nonneg_right hpow hpoly).trans hcheck

theorem safeFamily_le_rational2523 (index : ℕ) (i : Fin 30) (W U B : ℝ)
    (hw : Real.exp (ownerRad_2463 i / 2) ≤ W)
    (hu : ownerProductionExpUpper2514 index i ≤ U) (hu0 : 0 ≤ U)
    (hf : 0 ≤ safeFactor2523 (|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)
      (ownerMod_2463 i) (ownerRad_2463 i) (ownerProductionT2516 index i))
    (hb : W * (U * safeFactor2523 (|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|)
      (ownerMod_2463 i) (ownerRad_2463 i) (ownerProductionT2516 index i)) ≤ B) :
    safeFamily2523 index i ≤ B := by
  unfold safeFamily2523
  exact ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu hf)
    (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right hw (mul_nonneg hu0 hf))).trans hb

theorem production_t_reflect2523 (index : ℕ) (hi : index ≤ 639) (i : Fin 30) :
    ownerProductionT2516 (639 - index) i = ownerProductionT2516 index i := by
  unfold ownerProductionT2516 ownerCellEndpointRatio2488
  rw [Nat.cast_sub hi]
  norm_num only [Nat.cast_ofNat]
  have hl : -stripRadius2303 + (639 - (index : ℝ)) * (stripRadius2303 / 320) =
      -(-stripRadius2303 + ((index : ℝ) + 1) * (stripRadius2303 / 320)) := by ring
  have hr : -stripRadius2303 + (639 - (index : ℝ) + 1) * (stripRadius2303 / 320) =
      -(-stripRadius2303 + (index : ℝ) * (stripRadius2303 / 320)) := by ring
  rw [hl, hr]
  simp only [abs_neg, max_comm]

theorem production_a_reflect2523 (index : ℕ) (hi : index ≤ 639) (i : Fin 30) :
    ownerCellLowerRatio2501 stripRadius2303 (stripRadius2303 / 320) (639 - index) i =
      ownerCellLowerRatio2501 stripRadius2303 (stripRadius2303 / 320) index i := by
  unfold ownerCellLowerRatio2501
  rw [Nat.cast_sub hi]
  norm_num only [Nat.cast_ofNat]
  have hl : -stripRadius2303 + (639 - (index : ℝ)) * (stripRadius2303 / 320) =
      -(-stripRadius2303 + ((index : ℝ) + 1) * (stripRadius2303 / 320)) := by ring
  have hr : -stripRadius2303 + (639 - (index : ℝ) + 1) * (stripRadius2303 / 320) =
      -(-stripRadius2303 + (index : ℝ) * (stripRadius2303 / 320)) := by ring
  rw [hl, hr]
  simp only [abs_neg, neg_nonpos, neg_nonneg, and_comm, min_comm]

theorem safeFamily_reflect2523 (index : ℕ) (hi : index ≤ 639) (i : Fin 30) :
    safeFamily2523 (639 - index) i = safeFamily2523 index i := by
  unfold safeFamily2523 ownerProductionExpUpper2514
  rw [production_a_reflect2523 index hi i, production_t_reflect2523 index hi i]

theorem safeSum_reflect2523 (index : ℕ) (hi : index ≤ 639) :
    (∑ i : Fin 30, safeFamily2523 (639 - index) i) =
      ∑ i : Fin 30, safeFamily2523 index i := by
  exact Finset.sum_congr rfl (fun i _ => safeFamily_reflect2523 index hi i)

end ConnesWeilRH.Dev
