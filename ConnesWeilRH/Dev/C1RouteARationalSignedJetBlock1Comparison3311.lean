import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309

namespace ConnesWeilRH.Dev

/-
Record 3311 block-0 arithmetic mirror.

The rectangle upper is generated from the finite rational operations mirrored
by `routea_signed_jet_rect_arb_probe_3311.py`, then rounded upward to 10^-80.
The external Arb computation is not imported as a theorem; this file proves
only the exact comparison of the recorded rational constants.
-/

def routeASignedJetRectBlock1Upper3311 : ℚ := 15708713737333833816569243919607100148830399279490171/10000000000000000000000000000000000000000000000000000000000000000000000000000000

def routeACorrectedSignedBlock1Upper3309 : ℚ := 638555948777598291530785796926987531383394630734210916454392625570559/100000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem routeASignedJetRectBlock1Upper3311_le_manifest3309 :
    routeASignedJetRectBlock1Upper3311 ≤
      routeACorrectedSignedBlock1Upper3309 := by
  norm_num [routeASignedJetRectBlock1Upper3311,
    routeACorrectedSignedBlock1Upper3309]

end ConnesWeilRH.Dev
