import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P058 : ℚ := ((-85785680042140791506615089198057767288973398516845169 : ℚ) / 2571258080794422023720555088261737962950337180467200)

def momentPanelGrowth2622K01P058 : ℚ := ((898999958538446991516348542319807353922056907251611 : ℚ) / 3743206842467603331054540154925954656812620002099200)

theorem momentPanelPhase_owner2622K01P058 :
    (momentPanelPhase2622K01P058 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-63 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P058 :
    (momentPanelGrowth2622K01P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P058Input : RatPair2542 := (momentPanelPhase2622K01P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P058Expected : RatState2542 :=
  ((((3459929526030333968987095526244846917955208788774181293626676372798041850834484579 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8772242591678181602701460096602191 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P058_replay :
    compactExp2620 momentScalarAmp2622K01P058Input 20 = momentScalarAmp2622K01P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K01P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P058_replay] at h
  simpa only [momentPanelPhase_owner2622K01P058] using h

theorem momentScalarAmp2622K01P058_radius_le :
    (momentScalarAmp2622K01P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P058Expected]

def momentScalarGrow2622K01P058Input : RatPair2542 := (momentPanelGrowth2622K01P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P058Expected : RatState2542 :=
  ((((678957245704394160855052070053994074220129115735881358136521382015851872056176769797071447209303 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3442721451656564061273799394411494361567295370971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P058_replay :
    compactExp2620 momentScalarGrow2622K01P058Input 20 = momentScalarGrow2622K01P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P058] using h

theorem momentScalarGrow2622K01P058_radius_le :
    (momentScalarGrow2622K01P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P058Expected]

end ConnesWeilRH.Dev
