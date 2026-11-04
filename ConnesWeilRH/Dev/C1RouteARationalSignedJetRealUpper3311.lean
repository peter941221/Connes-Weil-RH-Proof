import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310
import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309

namespace ConnesWeilRH.Dev

def ratWeightedPhysicalBlockRealUpper3311 (order block : ℕ) : ℚ :=
  (ratWeightedPhysicalBlockRect3310 order block).reHi

theorem ratWeightedPhysicalBlockRealUpper3311_spec
    {order block : ℕ} (horder : order ≤ 6) (hblock : block < 160) :
    ((∑ offset ∈ Finset.range 256,
        iteratedDeriv order
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584)
          (record2680Center3212 (block * 256 + offset))).re : ℝ) ≤
      ratWeightedPhysicalBlockRealUpper3311 order block := by
  have hmem := ratWeightedPhysicalBlockRect_mem3310 horder hblock
  change _ ≤ ((ratWeightedPhysicalBlockRect3310 order block).reHi : ℝ)
  exact hmem.2.1

theorem ratWeightedPhysicalBlockRealUpper3311_order0_spec
    {block : ℕ} (hblock : block < 160) :
    ((∑ offset ∈ Finset.range 256,
        (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584
          (record2680Center3212 (block * 256 + offset)))).re : ℝ) ≤
      ratWeightedPhysicalBlockRealUpper3311 0 block := by
  simpa [weightedPhysical2539, ratWeightedPhysicalBlockRealUpper3311] using
    ratWeightedPhysicalBlockRealUpper3311_spec (order := 0) (by norm_num) hblock

end ConnesWeilRH.Dev
