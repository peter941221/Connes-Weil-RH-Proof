import ConnesWeilRH.Dev.C1SeedIntervalJet2734
import ConnesWeilRH.Dev.C1RouteBSeedCellGeometry2809

/-!
Record 2838: the first concrete Lean-side Route B bridge target.

This file specializes the already proved interval-jet enclosure to cell 4096
and order 4.  It deliberately does not identify the Lean interval with the
Python `p3.seed_jet` artifact; that semantic equality/inclusion remains open.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeB_cell4096_order4_mem2838 {x : ℝ}
    (hx : (routeBSeedCell2809 4096).Mem x) :
    (seedTransitionJetInterval2734 (routeBSeedCell2809 4096) 4).Mem
      (iteratedDeriv 4 Real.smoothTransition x) := by
  exact seedTransitionJetInterval_mem2734 (routeBSeedCell2809 4096) 4
    (routeBSeedCell2809_mem_unit 4096 (by norm_num)).1
    (routeBSeedCell2809_mem_unit 4096 (by norm_num)).2 hx

theorem routeB_cell4096_order4_norm_bound2838 {x : ℝ}
    (hx : (routeBSeedCell2809 4096).Mem x) :
    ‖iteratedDeriv 4 Real.smoothTransition x‖ ≤
      (seedTransitionJetInterval2734 (routeBSeedCell2809 4096) 4).endpointAbsMax := by
  exact norm_iteratedDeriv_le_seedCellJet2734 (routeBSeedCell2809 4096) 4
    (routeBSeedCell2809_mem_unit 4096 (by norm_num)).1
    (routeBSeedCell2809_mem_unit 4096 (by norm_num)).2 hx

theorem routeB_cell4096_order4_interval2838 :
    (routeBSeedCell2809 4096).lo = (8392704 : ℝ) / 33554432 ∧
      (routeBSeedCell2809 4096).hi = (8394751 : ℝ) / 33554432 := by
  norm_num [routeBSeedCell2809]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
