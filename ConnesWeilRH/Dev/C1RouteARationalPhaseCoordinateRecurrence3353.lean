import ConnesWeilRH.Dev.C1RouteARationalPhaseCoordinatePropagation3352

namespace ConnesWeilRH.Dev

mutual
  def ratPhasePowSqRealBound3353 : ℕ → ℚ
    | 0 => 1
    | n + 1 =>
        ratPhasePowSqRealBound3353 n * ratPhasePowSqRealBound3353 n +
          ratPhasePowSqImagBound3353 n * ratPhasePowSqImagBound3353 n

  def ratPhasePowSqImagBound3353 : ℕ → ℚ
    | 0 => 1 / 2
    | n + 1 =>
        2 * ratPhasePowSqRealBound3353 n * ratPhasePowSqImagBound3353 n
end

theorem ratPhasePowSqRealBound3353_nonneg :
    ∀ n, 0 ≤ ratPhasePowSqRealBound3353 n
  | 0 => by norm_num [ratPhasePowSqRealBound3353]
  | n + 1 => by
      rw [ratPhasePowSqRealBound3353]
      exact add_nonneg
        (mul_self_nonneg _)
        (mul_self_nonneg _)

theorem ratPhasePowSqImagBound3353_nonneg :
    ∀ n, 0 ≤ ratPhasePowSqImagBound3353 n
  | 0 => by norm_num [ratPhasePowSqImagBound3353]
  | n + 1 => by
      rw [ratPhasePowSqImagBound3353]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (ratPhasePowSqRealBound3353_nonneg n))
        (ratPhasePowSqImagBound3353_nonneg n)

theorem ratPhasePowSqCoordinateBounds3353_cell0_family4 :
    ∀ n,
      ratRectRealEndpointAbsBound3352
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) n) ≤
        ratPhasePowSqRealBound3353 n ∧
      ratRectImagEndpointAbsBound3352
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) n) ≤
        ratPhasePowSqImagBound3353 n := by
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [RatRect3276.powSq, ratPhasePowSqRealBound3353] using
          ratPhaseRealEndpointAbsBound3351_cell0_family4
      · simpa [RatRect3276.powSq, ratPhasePowSqImagBound3353] using
          ratPhaseImagEndpointAbsBound3351_cell0_family4
  | succ n ih =>
      rw [RatRect3276.powSq]
      constructor
      · apply ratRect_mul_square_re_abs_le3352
        · exact ih.1
        · exact ih.2
        · exact ratPhasePowSqRealBound3353_nonneg n
        · exact ratPhasePowSqImagBound3353_nonneg n
      · apply ratRect_mul_square_im_abs_le3352
        · exact ih.1
        · exact ih.2
        · exact ratPhasePowSqRealBound3353_nonneg n
        · exact ratPhasePowSqImagBound3353_nonneg n

theorem ratPhasePowSqCoordinateBounds3353_cell0_family4_nine :
    ratRectRealEndpointAbsBound3352
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) 9) ≤
        ratPhasePowSqRealBound3353 9 ∧
      ratRectImagEndpointAbsBound3352
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) 9) ≤
        ratPhasePowSqImagBound3353 9 := by
  exact ratPhasePowSqCoordinateBounds3353_cell0_family4 9

end ConnesWeilRH.Dev
