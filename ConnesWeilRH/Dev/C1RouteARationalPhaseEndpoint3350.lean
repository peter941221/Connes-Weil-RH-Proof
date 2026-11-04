import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349
import ConnesWeilRH.Dev.C1RouteARationalPhaseEndpoint3348

namespace ConnesWeilRH.Dev

def ratPhasePowSqBound3350 : ℕ → ℚ
  | 0 => 2
  | n + 1 => 2 * ratPhasePowSqBound3350 n *
      ratPhasePowSqBound3350 n

theorem ratPhasePowSqBound3350_nonneg :
    ∀ n, 0 ≤ ratPhasePowSqBound3350 n
  | 0 => by norm_num [ratPhasePowSqBound3350]
  | n + 1 => by
      rw [ratPhasePowSqBound3350]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (ratPhasePowSqBound3350_nonneg n))
        (ratPhasePowSqBound3350_nonneg n)

theorem ratPhasePowSqBound3350_zero :
    ratPhasePowSqBound3350 0 = 2 := by
  rfl

theorem ratPhasePowSqBound3350_step (n : ℕ) :
    2 * ratPhasePowSqBound3350 n * ratPhasePowSqBound3350 n =
      ratPhasePowSqBound3350 (n + 1) := by
  rfl

theorem ratPhasePowSqEndpointAbsBound3350_cell0_family4 :
    ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4)) 9) ≤
      ratPhasePowSqBound3350 9 := by
  have hbase := ratPhaseRectEndpointAbsBound3348_cell0_family4
  have hpow : ∀ n : ℕ,
      ratRectEndpointAbsBound3326
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) n) ≤
        ratPhasePowSqBound3350 n := by
    intro n
    induction n with
    | zero =>
        simpa [RatRect3276.powSq, ratPhasePowSqBound3350_zero] using hbase
    | succ n ih =>
        rw [RatRect3276.powSq]
        have hmul := ratRect_mul_endpointAbsBound3349
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) n)
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) n)
        exact le_trans hmul (by
          have hnonneg := ratRectEndpointAbsBound3326_nonneg
            (RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 0 4)) n)
          calc
            2 * ratRectEndpointAbsBound3326
                (RatRect3276.powSq
                  (ratPhaseRect3279
                    (record2680PhaseAngleRat3279 0 4)) n) *
                ratRectEndpointAbsBound3326
                  (RatRect3276.powSq
                    (ratPhaseRect3279
                      (record2680PhaseAngleRat3279 0 4)) n) ≤
                2 * ratPhasePowSqBound3350 n *
                  ratPhasePowSqBound3350 n := by
              gcongr
              exact mul_nonneg (by norm_num)
                (ratPhasePowSqBound3350_nonneg n)
            _ = ratPhasePowSqBound3350 (n + 1) :=
              ratPhasePowSqBound3350_step n)
  exact hpow 9

end ConnesWeilRH.Dev
