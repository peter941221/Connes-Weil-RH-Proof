import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349
import ConnesWeilRH.Dev.C1RouteARationalPhaseEndpoint3375

namespace ConnesWeilRH.Dev

def ratPhasePowSqBound3376 : ℕ → ℚ
  | 0 => 2
  | n + 1 => 2 * ratPhasePowSqBound3376 n *
      ratPhasePowSqBound3376 n

theorem ratPhasePowSqBound3376_nonneg :
    ∀ n, 0 ≤ ratPhasePowSqBound3376 n
  | 0 => by norm_num [ratPhasePowSqBound3376]
  | n + 1 => by
      rw [ratPhasePowSqBound3376]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (ratPhasePowSqBound3376_nonneg n))
        (ratPhasePowSqBound3376_nonneg n)

theorem ratPhasePowSqBound3376_zero :
    ratPhasePowSqBound3376 0 = 2 := by
  rfl

theorem ratPhasePowSqBound3376_step (n : ℕ) :
    2 * ratPhasePowSqBound3376 n * ratPhasePowSqBound3376 n =
      ratPhasePowSqBound3376 (n + 1) := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratPhasePowSqEndpointAbsBound3376_cell1_family4_nine :
    ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) ≤
      ratPhasePowSqBound3376 9 := by
  have hbase := ratPhaseRectEndpointAbsBound3375_cell1_family4
  have hpow : ∀ n : ℕ,
      ratRectEndpointAbsBound3326
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) n) ≤
        ratPhasePowSqBound3376 n := by
    intro n
    induction n with
    | zero =>
        simpa [RatRect3276.powSq, ratPhasePowSqBound3376_zero] using hbase
    | succ n ih =>
        rw [RatRect3276.powSq]
        have hmul := ratRect_mul_endpointAbsBound3349
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) n)
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) n)
        exact le_trans hmul (by
          have hnonneg := ratRectEndpointAbsBound3326_nonneg
            (RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 1 4)) n)
          calc
            2 * ratRectEndpointAbsBound3326
                (RatRect3276.powSq
                  (ratPhaseRect3279
                    (record2680PhaseAngleRat3279 1 4)) n) *
                ratRectEndpointAbsBound3326
                  (RatRect3276.powSq
                    (ratPhaseRect3279
                      (record2680PhaseAngleRat3279 1 4)) n) ≤
                2 * ratPhasePowSqBound3376 n *
                  ratPhasePowSqBound3376 n := by
              gcongr
              exact mul_nonneg (by norm_num)
                (ratPhasePowSqBound3376_nonneg n)
            _ = ratPhasePowSqBound3376 (n + 1) :=
              ratPhasePowSqBound3376_step n)
  exact hpow 9

end ConnesWeilRH.Dev
