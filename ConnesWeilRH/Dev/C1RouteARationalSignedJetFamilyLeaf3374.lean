import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermCell0Budget3373

namespace ConnesWeilRH.Dev

def routeASignedJetFamilyLeafUpper3374 : ℚ := 7

theorem routeASignedJetFamilyLeafUpper3374_spec :
    (ratWeightedPhysicalTermRect3310 2 0 4).reHi ≤
      routeASignedJetFamilyLeafUpper3374 := by
  exact le_trans
    ratWeightedPhysicalTermRect_cell0_order2_family4_reHi_le3373
    (by norm_num [routeASignedJetFamilyLeafUpper3374])

end ConnesWeilRH.Dev
