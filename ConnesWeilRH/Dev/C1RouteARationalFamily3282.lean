import ConnesWeilRH.Dev.C1RouteARationalCoefficient3282

namespace ConnesWeilRH.Dev

theorem ratCanonicalFamilyRect_mem3282
    {index : ℕ} (hindex : index < 40960) (family : Fin 30)
    {bumpInterval : RatInterval3276}
    (hactive : |record2680Center3212 index| <
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
    (hbump : bumpInterval.Mem
      (C1RouteAOwnerScaleAudit.widthBump
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index))) :
    (RatRect3276.mul
      (RatRect3276.mul (ratCoefficientRect3282 family)
        (ratRealRect3281 bumpInterval))
      (RatRect3276.powSq
        (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)) 9)).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family)
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index)) := by
  apply ratFamilyRect_mem3281
  · exact ratCoefficientRect_mem3282 family
  · exact hbump
  · exact record2680CanonicalPhasePowRect_mem3279 hindex family hactive

end ConnesWeilRH.Dev
