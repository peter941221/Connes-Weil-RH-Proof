import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P036 : ℚ := ((-120121938932494501584624799349822407751972634296701601 : ℚ) / 2716623258296524037606341514250169042590919924121600)

def momentPanelGrowth2622K02P036 : ℚ := ((307319506037304399450715044846597689957256549308900439 : ℚ) / 447647818055837351530633150430614397505143820412518400)

theorem momentPanelPhase_owner2622K02P036 :
    (momentPanelPhase2622K02P036 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-107 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P036 :
    (momentPanelGrowth2622K02P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P036Input : RatPair2542 := (momentPanelPhase2622K02P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P036Expected : RatState2542 :=
  ((((133732914801657491397846774012786538415493147617815724202308511683183911808383 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((169536176483688710781078044887 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P036_replay :
    compactExp2620 momentScalarAmp2622K02P036Input 20 = momentScalarAmp2622K02P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K02P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P036_replay] at h
  simpa only [momentPanelPhase_owner2622K02P036] using h

theorem momentScalarAmp2622K02P036_radius_le :
    (momentScalarAmp2622K02P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P036Expected]

def momentScalarGrow2622K02P036Input : RatPair2542 := (momentPanelGrowth2622K02P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P036Expected : RatState2542 :=
  ((((1060939905835702734188661950816333177261864541895716580556858402012997841071252240285246902880935 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1344900227909128615035029612380900512441859311243 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P036_replay :
    compactExp2620 momentScalarGrow2622K02P036Input 20 = momentScalarGrow2622K02P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P036] using h

theorem momentScalarGrow2622K02P036_radius_le :
    (momentScalarGrow2622K02P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P036Expected]

end ConnesWeilRH.Dev
