import ConnesWeilRH.Dev.C1RouteARationalRealMulCommutativity3360

namespace ConnesWeilRH.Dev

theorem ratWeightedPhaseRect_orientation3361
    (cell : ℕ) (family : Fin 30) :
    ratWeightedPhaseRect3310 cell family =
      RatRect3276.mul
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 cell family)) 9)
        (ratRealRect3281 (ratCellWeightInterval3289 cell)) := by
  unfold ratWeightedPhaseRect3310
  exact ratRect_mul_real_comm3360 _ _

end ConnesWeilRH.Dev
