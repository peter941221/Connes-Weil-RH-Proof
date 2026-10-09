import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P129 : ℚ := ((-29540386275888809844297019207664503975 : ℚ) / 912951821079568989122713674886152192)

def momentPanelGrowth2622K07P129 : ℚ := ((2509672023162730827467770829994625 : ℚ) / 5963028423473591104640491878088704)

theorem momentPanelPhase_owner2622K07P129 :
    (momentPanelPhase2622K07P129 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P129 :
    (momentPanelGrowth2622K07P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P129Input : RatPair2542 := (momentPanelPhase2622K07P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P129Expected : RatState2542 :=
  ((((4732276061734938567637238096698559596332140339246803669692230104345983492689322717 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5999057707040391848735543634365945 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P129_replay :
    compactExp2620 momentScalarAmp2622K07P129Input 20 = momentScalarAmp2622K07P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K07P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P129_replay] at h
  simpa only [momentPanelPhase_owner2622K07P129] using h

theorem momentScalarAmp2622K07P129_radius_le :
    (momentScalarAmp2622K07P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P129Expected]

def momentScalarGrow2622K07P129Input : RatPair2542 := (momentPanelGrowth2622K07P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P129Expected : RatState2542 :=
  ((((1626863170789619813849324898549304097689184192329217851361645575583518546189765400901966818768551 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1031146623593907225218544533451331604038334469627 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P129_replay :
    compactExp2620 momentScalarGrow2622K07P129Input 20 = momentScalarGrow2622K07P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P129] using h

theorem momentScalarGrow2622K07P129_radius_le :
    (momentScalarGrow2622K07P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P129Expected]

end ConnesWeilRH.Dev
