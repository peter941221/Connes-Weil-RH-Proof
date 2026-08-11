import ConnesWeilRH.Dev.Wall14PlateauBumpHI
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set
open scoped Topology

#check IntegrableOn.mono_set
#check IntegrableOn.mono
#check IntegrableOn.norm
#check MeasureTheory.integral_mono
#check MeasureTheory.integral_mono_ae
#check Real.volume_Ioc
#check integrableOn_exp_neg_Ioi