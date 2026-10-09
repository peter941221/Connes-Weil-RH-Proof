import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P031 : ℚ := ((-2482240447365300182129040603249977179803 : ℚ) / 53365047908167910052447612858636697600)

def momentPanelGrowth2622K25P031 : ℚ := ((12189119404454275446825044265690489430403 : ℚ) / 14365814714604199270991823047658936729600)

theorem momentPanelPhase_owner2622K25P031 :
    (momentPanelPhase2622K25P031 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P031 :
    (momentPanelGrowth2622K25P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P031Input : RatPair2542 := (momentPanelPhase2622K25P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P031Expected : RatState2542 :=
  ((((13448493520981223897282005827383257727220629324144524668633090310791805346943 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4262791248369752125911046039 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K25P031_replay :
    compactExp2620 momentScalarAmp2622K25P031Input 20 = momentScalarAmp2622K25P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K25P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P031_replay] at h
  simpa only [momentPanelPhase_owner2622K25P031] using h

theorem momentScalarAmp2622K25P031_radius_le :
    (momentScalarAmp2622K25P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P031Expected]

def momentScalarGrow2622K25P031Input : RatPair2542 := (momentPanelGrowth2622K25P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P031Expected : RatState2542 :=
  ((((1247467368846267702964245106162960120981742365185904696361190818109845519456818165957231682583353 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3162702958586763289313264113054470515319724058649 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K25P031_replay :
    compactExp2620 momentScalarGrow2622K25P031Input 20 = momentScalarGrow2622K25P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P031] using h

theorem momentScalarGrow2622K25P031_radius_le :
    (momentScalarGrow2622K25P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P031Expected]

end ConnesWeilRH.Dev
