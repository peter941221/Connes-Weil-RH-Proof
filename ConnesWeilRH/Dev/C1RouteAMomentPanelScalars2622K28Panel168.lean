import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P168 : ℚ := ((-798678109882860409186906188078143871839 : ℚ) / 10378508994188559755933808483054387200)

def momentPanelGrowth2622K28P168 : ℚ := ((16097082558531855165508062265950047854963 : ℚ) / 4776534842912933314594650006646004121600)

theorem momentPanelPhase_owner2622K28P168 :
    (momentPanelPhase2622K28P168 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P168 :
    (momentPanelGrowth2622K28P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P168Input : RatPair2542 := (momentPanelPhase2622K28P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P168Expected : RatState2542 :=
  ((((202492456381756910109835869214874054024449654477590868404947113 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((604462910064023133916467 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K28P168_replay :
    compactExp2620 momentScalarAmp2622K28P168Input 20 = momentScalarAmp2622K28P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K28P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P168_replay] at h
  simpa only [momentPanelPhase_owner2622K28P168] using h

theorem momentScalarAmp2622K28P168_radius_le :
    (momentScalarAmp2622K28P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P168Expected]

def momentScalarGrow2622K28P168Input : RatPair2542 := (momentPanelGrowth2622K28P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P168Expected : RatState2542 :=
  ((((15528359799222579467487227721663833753489855469615958607372949175290847630698196323043488589317271 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((78737885422945699109449242268267187096836011035303 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K28P168_replay :
    compactExp2620 momentScalarGrow2622K28P168Input 20 = momentScalarGrow2622K28P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P168] using h

theorem momentScalarGrow2622K28P168_radius_le :
    (momentScalarGrow2622K28P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P168Expected]

end ConnesWeilRH.Dev
