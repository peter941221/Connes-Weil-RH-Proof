import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309

namespace ConnesWeilRH.Dev

/-
Record 3311 block-0 arithmetic mirror.

The rectangle upper is generated from the finite rational operations mirrored
by `routea_signed_jet_rect_arb_probe_3311.py`, then rounded upward to 10^-80.
The external Arb computation is not imported as a theorem; this file proves
only the exact comparison of the recorded rational constants.
-/

def routeASignedJetRectBlock0Upper3311 : ℚ := 27813974097948817242298065574442126536461551723492123/12500000000000000000000000000000000000000000000000000000000000000000000000000000

def routeACorrectedSignedBlock0Upper3309 : ℚ := 159638987194399589238860301794796826021678655516372647828511845675221/25000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem routeASignedJetRectBlock0Upper3311_le_manifest3309 :
    routeASignedJetRectBlock0Upper3311 ≤
      routeACorrectedSignedBlock0Upper3309 := by
  norm_num [routeASignedJetRectBlock0Upper3311,
    routeACorrectedSignedBlock0Upper3309]

end ConnesWeilRH.Dev
