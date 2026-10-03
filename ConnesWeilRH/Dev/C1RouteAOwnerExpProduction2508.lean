import ConnesWeilRH.Dev.C1RouteAOwnerLowerRatioProduction2507
import ConnesWeilRH.Dev.C1RouteAOwnerExpAuto2506

/-! Record 2508: production lower-ratio to automatic exponential consumer.

This is the direct composition of the audited 2507 domain certificate with
the 2506 floor-selected split.  It introduces no stored split index or
floating-point payload.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem ownerCellExpSplitUpper_production2508
    {index : ℕ} (hlo : 196 ≤ index) (hhi : index ≤ 443)
    (i : Fin 30) :
    Real.exp (-(30 /
      (1 - (ownerCellLowerRatio2501 stripRadius2303
        (stripRadius2303 / 320) index i) ^ 2))) ≤
      expNegOneUpper2498 ^
          (⌊30 /
            (1 - (ownerCellLowerRatio2501 stripRadius2303
              (stripRadius2303 / 320) index i) ^ 2)⌋₊ : ℕ) *
        (expTaylor20
            (30 /
              (1 - (ownerCellLowerRatio2501 stripRadius2303
                (stripRadius2303 / 320) index i) ^ 2) -
              (⌊30 /
                (1 - (ownerCellLowerRatio2501 stripRadius2303
                  (stripRadius2303 / 320) index i) ^ 2)⌋₊ : ℕ)) +
          expTaylor20Error) := by
  exact ownerCellExpSplitUpper_auto_of_lowerRatio2506 i
    (ownerCellLowerRatio_lt_one_production2507 hlo hhi i)

end ConnesWeilRH.Dev
