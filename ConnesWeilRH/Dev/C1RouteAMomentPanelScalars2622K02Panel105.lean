import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P105 : ℚ := ((-111825866945779403211266290496885161907711716140158363 : ℚ) / 3714554845036531186442295064089256041949736363622400)

def momentPanelGrowth2622K02P105 : ℚ := ((2505451344716657570274377079544500821784345778321733 : ℚ) / 17644635050615970221559271954513273522558981688524800)

theorem momentPanelPhase_owner2622K02P105 :
    (momentPanelPhase2622K02P105 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P105 :
    (momentPanelGrowth2622K02P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P105Input : RatPair2542 := (momentPanelPhase2622K02P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P105Expected : RatState2542 :=
  ((((11249612543405964440356123020315864203436842414138632959117131159495110740243492055 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((57043950089860139737174054449254993 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P105_replay :
    compactExp2620 momentScalarAmp2622K02P105Input 20 = momentScalarAmp2622K02P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K02P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P105_replay] at h
  simpa only [momentPanelPhase_owner2622K02P105] using h

theorem momentScalarAmp2622K02P105_radius_le :
    (momentScalarAmp2622K02P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P105Expected]

def momentScalarGrow2622K02P105Input : RatPair2542 := (momentPanelGrowth2622K02P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P105Expected : RatState2542 :=
  ((((615469165951456828713915532780475881858612960892444020368655458570442930509670861261632363388501 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3120799007951873713705379816225058116518838322267 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P105_replay :
    compactExp2620 momentScalarGrow2622K02P105Input 20 = momentScalarGrow2622K02P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P105] using h

theorem momentScalarGrow2622K02P105_radius_le :
    (momentScalarGrow2622K02P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P105Expected]

end ConnesWeilRH.Dev
