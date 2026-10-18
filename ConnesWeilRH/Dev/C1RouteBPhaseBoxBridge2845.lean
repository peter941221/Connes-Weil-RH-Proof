import ConnesWeilRH.Dev.C1RouteBRationalReplay2844
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def routeBCell4096Interval2845 : RealInterval2429 :=
  { lo := (8392704 : ℝ) / 33554432
    hi := (8394751 : ℝ) / 33554432 }

def routeBPhaseContains2845 (n : ℕ) : Prop :=
  (routeBPhase2844 n).lo ≤
      (phaseJetInterval2734 routeBCell4096Interval2845 n).lo ∧
    (phaseJetInterval2734 routeBCell4096Interval2845 n).hi ≤
      (routeBPhase2844 n).hi

theorem routeB_phase_box_contains_lean_interval2845 (n : ℕ) (hn : n ≤ 7) :
    routeBPhaseContains2845 n := by
  interval_cases n <;>
    norm_num [routeBPhaseContains2845, routeBPhase2844,
      routeBCell4096Interval2845, phaseJetInterval2734,
      reciprocalJetInterval2734, sumJetIntervals2734,
      Finset.sum_range_succ, coordinateJetInterval2734,
      reflectedCoordinateJetInterval2734, RealInterval2429.point,
      RealInterval2429.sub, RealInterval2429.mul,
      RealInterval2429.invPositive]

end
end ConnesWeilRH.Dev
