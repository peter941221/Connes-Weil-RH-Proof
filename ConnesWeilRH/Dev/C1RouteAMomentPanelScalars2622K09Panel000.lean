import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P000 : ℚ := ((-818755290837800380696519764462458988303 : ℚ) / 5380923267848788163473205766180044800)

def momentPanelGrowth2622K09P000 : ℚ := ((5481920710962892511094735533286218209 : ℚ) / 366097493345912651152247885712588800)

theorem momentPanelPhase_owner2622K09P000 :
    (momentPanelPhase2622K09P000 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-179 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P000, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P000 :
    (momentPanelGrowth2622K09P000 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (-179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P000, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P000Input : RatPair2542 := (momentPanelPhase2622K09P000 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P000Expected : RatState2542 :=
  ((((884716228934563306831587223617 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K09P000_replay :
    compactExp2620 momentScalarAmp2622K09P000Input 20 = momentScalarAmp2622K09P000Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P000_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-179 / 200) 0) -
      (momentScalarAmp2622K09P000Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P000]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P000 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P000 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P000Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P000_replay] at h
  simpa only [momentPanelPhase_owner2622K09P000] using h

theorem momentScalarAmp2622K09P000_radius_le :
    (momentScalarAmp2622K09P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P000Expected]

def momentScalarGrow2622K09P000Input : RatPair2542 := (momentPanelGrowth2622K09P000 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P000Expected : RatState2542 :=
  ((((1700735298592640509978836880910584116927163963786461563551559372722584755106615787959906826393788471657 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((8623629339822289788400557353952360288661749107792211703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P000_replay :
    compactExp2620 momentScalarGrow2622K09P000Input 20 = momentScalarGrow2622K09P000Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P000_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P000Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P000]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P000 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P000 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P000Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P000_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P000] using h

theorem momentScalarGrow2622K09P000_radius_le :
    (momentScalarGrow2622K09P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P000Expected]

end ConnesWeilRH.Dev
