import ConnesWeilRH.Dev.C1RouteARationalSignedJetInactive3320

namespace ConnesWeilRH.Dev

def probe3321 : ℚ := (ratWeightedPhysicalTermRect3310 2 0 4).reHi

#eval (List.range 3001).filter (fun exponent =>
  decide (probe3321 ≤ 1 / (10 : ℚ) ^ exponent))

end ConnesWeilRH.Dev
