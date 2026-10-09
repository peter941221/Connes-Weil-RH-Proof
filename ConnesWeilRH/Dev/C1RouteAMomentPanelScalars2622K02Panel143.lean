import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P143 : ℚ := ((-108237691900459079384700955762096814069266825543298399 : ℚ) / 2716623258296524037606341514250169042590919924121600)

def momentPanelGrowth2622K02P143 : ℚ := ((307319506037304399450715044846597689957256549308900439 : ℚ) / 447647818055837351530633150430614397505143820412518400)

theorem momentPanelPhase_owner2622K02P143 :
    (momentPanelPhase2622K02P143 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P143 :
    (momentPanelGrowth2622K02P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P143Input : RatPair2542 := (momentPanelPhase2622K02P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P143Expected : RatState2542 :=
  ((((5309945323318084262627751555032218314216023000810034154219553491516881073619889 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((13462824707423826560799476532807 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P143_replay :
    compactExp2620 momentScalarAmp2622K02P143Input 20 = momentScalarAmp2622K02P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K02P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P143_replay] at h
  simpa only [momentPanelPhase_owner2622K02P143] using h

theorem momentScalarAmp2622K02P143_radius_le :
    (momentScalarAmp2622K02P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P143Expected]

def momentScalarGrow2622K02P143Input : RatPair2542 := (momentPanelGrowth2622K02P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P143Expected : RatState2542 :=
  ((((1060939905835702734188661950816333177261864541895716580556858402012997841071252240285246902880935 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1344900227909128615035029612380900512441859311243 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P143_replay :
    compactExp2620 momentScalarGrow2622K02P143Input 20 = momentScalarGrow2622K02P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P143] using h

theorem momentScalarGrow2622K02P143_radius_le :
    (momentScalarGrow2622K02P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P143Expected]

end ConnesWeilRH.Dev
