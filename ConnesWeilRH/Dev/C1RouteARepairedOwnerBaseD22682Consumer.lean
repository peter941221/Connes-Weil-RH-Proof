import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22681
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family1
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family2
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family3
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family4
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family5
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family6
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family7
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family8
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family9
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family10
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family11
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family12
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family13
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family14
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family15
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family16
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family17
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family18
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family19
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family20
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family21
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family22
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family23
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family24
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family25
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family26
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family27
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family28
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Family29

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2682: all repaired-owner base-D2 family bridges feed the existing
   cell consumer.  The cell and channel remain exactly those of record 2676. -/

theorem record2682RepairedOwnerBaseD2CellContained {position : ℝ}
    (hposition : position ∈ Set.Icc 0 record2675CellRight) :
    record2675BaseD2Rect.Mem
      (deriv (deriv (correctedPhysical record2678BaseCoefficient
        capturedModulations2584)) position) := by
  apply base_D2CellSumContained
  intro index x hx
  fin_cases index
  · exact record2681Family0BaseD2CellRectMem hx
  · exact record2681Family1BaseD2CellRectMem hx
  · exact record2681Family2BaseD2CellRectMem hx
  · exact record2681Family3BaseD2CellRectMem hx
  · exact record2681Family4BaseD2CellRectMem hx
  · exact record2681Family5BaseD2CellRectMem hx
  · exact record2681Family6BaseD2CellRectMem hx
  · exact record2681Family7BaseD2CellRectMem hx
  · exact record2681Family8BaseD2CellRectMem hx
  · exact record2681Family9BaseD2CellRectMem hx
  · exact record2681Family10BaseD2CellRectMem hx
  · exact record2681Family11BaseD2CellRectMem hx
  · exact record2681Family12BaseD2CellRectMem hx
  · exact record2681Family13BaseD2CellRectMem hx
  · exact record2681Family14BaseD2CellRectMem hx
  · exact record2681Family15BaseD2CellRectMem hx
  · exact record2681Family16BaseD2CellRectMem hx
  · exact record2681Family17BaseD2CellRectMem hx
  · exact record2681Family18BaseD2CellRectMem hx
  · exact record2681Family19BaseD2CellRectMem hx
  · exact record2681Family20BaseD2CellRectMem hx
  · exact record2681Family21BaseD2CellRectMem hx
  · exact record2681Family22BaseD2CellRectMem hx
  · exact record2681Family23BaseD2CellRectMem hx
  · exact record2681Family24BaseD2CellRectMem hx
  · exact record2681Family25BaseD2CellRectMem hx
  · exact record2681Family26BaseD2CellRectMem hx
  · exact record2681Family27BaseD2CellRectMem hx
  · exact record2681Family28BaseD2CellRectMem hx
  · exact record2681Family29BaseD2CellRectMem hx
  exact hposition

end ConnesWeilRH.Dev
