import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family0
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family1
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family2
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family3
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family4
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family5
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family6
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family7
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family8
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family9
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family10
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family11
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family12
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family13
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family14
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family15
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family16
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family17
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family18
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family19
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family20
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family21
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family22
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family23
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family24
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family25
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family26
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family27
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family28
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family29

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2683: all repaired-owner correction-D2 family bridges feed the
   existing correction-D2 cell consumer. -/

theorem record2683RepairedOwnerCorrectionD2CellContained {position : ℝ}
    (hposition : position ∈ Set.Icc 0 record2675CellRight) :
    record2675CorrectionD2Rect.Mem
      (deriv (deriv (correctedPhysical record2680CorrectionCoefficient
        capturedModulations2584)) position) := by
  apply correction_D2CellSumContained
  intro index x hx
  fin_cases index
  · exact record2683Family0CorrectionD2CellRectMem hx
  · exact record2683Family1CorrectionD2CellRectMem hx
  · exact record2683Family2CorrectionD2CellRectMem hx
  · exact record2683Family3CorrectionD2CellRectMem hx
  · exact record2683Family4CorrectionD2CellRectMem hx
  · exact record2683Family5CorrectionD2CellRectMem hx
  · exact record2683Family6CorrectionD2CellRectMem hx
  · exact record2683Family7CorrectionD2CellRectMem hx
  · exact record2683Family8CorrectionD2CellRectMem hx
  · exact record2683Family9CorrectionD2CellRectMem hx
  · exact record2683Family10CorrectionD2CellRectMem hx
  · exact record2683Family11CorrectionD2CellRectMem hx
  · exact record2683Family12CorrectionD2CellRectMem hx
  · exact record2683Family13CorrectionD2CellRectMem hx
  · exact record2683Family14CorrectionD2CellRectMem hx
  · exact record2683Family15CorrectionD2CellRectMem hx
  · exact record2683Family16CorrectionD2CellRectMem hx
  · exact record2683Family17CorrectionD2CellRectMem hx
  · exact record2683Family18CorrectionD2CellRectMem hx
  · exact record2683Family19CorrectionD2CellRectMem hx
  · exact record2683Family20CorrectionD2CellRectMem hx
  · exact record2683Family21CorrectionD2CellRectMem hx
  · exact record2683Family22CorrectionD2CellRectMem hx
  · exact record2683Family23CorrectionD2CellRectMem hx
  · exact record2683Family24CorrectionD2CellRectMem hx
  · exact record2683Family25CorrectionD2CellRectMem hx
  · exact record2683Family26CorrectionD2CellRectMem hx
  · exact record2683Family27CorrectionD2CellRectMem hx
  · exact record2683Family28CorrectionD2CellRectMem hx
  · exact record2683Family29CorrectionD2CellRectMem hx
  exact hposition

end ConnesWeilRH.Dev
