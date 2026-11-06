import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4BumpUniform3445
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk03446
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk103447
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk203448
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk303449
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk403450
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk503451
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk603452
import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4PhaseChunk703453

namespace ConnesWeilRH.Dev

theorem record2680_block0_family4_phase_abs_le_2_3454
    {index : ℕ} (hindex : index < 256) :
    ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 index 4)) 9) ≤ 2 := by
  rcases Nat.lt_or_ge index 32 with h0 | hrest0
  · exact record2680_block0_family4_phase_chunk0_abs_le_2_3446 h0
  rcases Nat.lt_or_ge index 64 with h1 | hrest1
  · exact record2680_block0_family4_phase_chunk1_abs_le_2_3447 hrest0 h1
  rcases Nat.lt_or_ge index 96 with h2 | hrest2
  · exact record2680_block0_family4_phase_chunk2_abs_le_2_3448 hrest1 h2
  rcases Nat.lt_or_ge index 128 with h3 | hrest3
  · exact record2680_block0_family4_phase_chunk3_abs_le_2_3449 hrest2 h3
  rcases Nat.lt_or_ge index 160 with h4 | hrest4
  · exact record2680_block0_family4_phase_chunk4_abs_le_2_3450 hrest3 h4
  rcases Nat.lt_or_ge index 192 with h5 | hrest5
  · exact record2680_block0_family4_phase_chunk5_abs_le_2_3451 hrest4 h5
  rcases Nat.lt_or_ge index 224 with h6 | hrest6
  · exact record2680_block0_family4_phase_chunk6_abs_le_2_3452 hrest5 h6
  exact record2680_block0_family4_phase_chunk7_abs_le_2_3453 hrest6 hindex

theorem record2680_block0_family4_bump_tail3454
    {index : ℕ} (hindex : index < 256) :
    ratCellBumpInterval3298 index 4 =
      ({lo := 0, hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi} :
        RatInterval3276) := by
  exact record2680_block0_family4_bump_tail3445 hindex

end ConnesWeilRH.Dev
