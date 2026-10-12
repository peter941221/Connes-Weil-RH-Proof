import ConnesWeilRH.Dev.C1RouteACellContainment2677Family0
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family1
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family2
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family3
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family4
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family5
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family6
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family7
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family8
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family9
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family10
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family11
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family12
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family13
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family14
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family15
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family16
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family17
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family18
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family19
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family20
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family21
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family22
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family23
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family24
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family25
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family26
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family27
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family28
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family29

namespace ConnesWeilRH.Dev

/- The exact Lean centers discharge every family premise of the base-M0
   aggregate consumer on cell 4096. The repaired binary64 owner is a later
   transport obligation and is intentionally not hidden here. -/

theorem record2677BaseM0ExactCentersCellContained
    {position : ℝ}
    (hposition : position ∈ Set.Icc 0 record2675CellRight) :
    record2675BaseM0Rect.Mem
      (externalPhysical2344
        (fun index => baseCoefficientCenter2540 index)
        (fun index => capturedModulations2584 index) position) := by
  apply record2677BaseM0CellContained
  · rfl
  · rfl
  · intro index hindex x hx
    fin_cases index
    · exact (hindex rfl).elim
    · exact record2677Family1BaseM0CellRectMem hx
    · exact record2677Family2BaseM0CellRectMem hx
    · exact record2677Family3BaseM0CellRectMem hx
    · exact record2677Family4BaseM0CellRectMem hx
    · exact record2677Family5BaseM0CellRectMem hx
    · exact record2677Family6BaseM0CellRectMem hx
    · exact record2677Family7BaseM0CellRectMem hx
    · exact record2677Family8BaseM0CellRectMem hx
    · exact record2677Family9BaseM0CellRectMem hx
    · exact record2677Family10BaseM0CellRectMem hx
    · exact record2677Family11BaseM0CellRectMem hx
    · exact record2677Family12BaseM0CellRectMem hx
    · exact record2677Family13BaseM0CellRectMem hx
    · exact record2677Family14BaseM0CellRectMem hx
    · exact record2677Family15BaseM0CellRectMem hx
    · exact record2677Family16BaseM0CellRectMem hx
    · exact record2677Family17BaseM0CellRectMem hx
    · exact record2677Family18BaseM0CellRectMem hx
    · exact record2677Family19BaseM0CellRectMem hx
    · exact record2677Family20BaseM0CellRectMem hx
    · exact record2677Family21BaseM0CellRectMem hx
    · exact record2677Family22BaseM0CellRectMem hx
    · exact record2677Family23BaseM0CellRectMem hx
    · exact record2677Family24BaseM0CellRectMem hx
    · exact record2677Family25BaseM0CellRectMem hx
    · exact record2677Family26BaseM0CellRectMem hx
    · exact record2677Family27BaseM0CellRectMem hx
    · exact record2677Family28BaseM0CellRectMem hx
    · exact record2677Family29BaseM0CellRectMem hx
  exact hposition

end ConnesWeilRH.Dev
