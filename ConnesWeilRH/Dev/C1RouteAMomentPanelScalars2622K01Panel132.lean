import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P132 : ℚ := ((-227866038901178172967608050106593917245092774247883 : ℚ) / 6237072417125044680224709686494293745992602746880)

def momentPanelGrowth2622K01P132 : ℚ := ((308329679252839924655015230056378379480409561754302891 : ℚ) / 790205211945003500430126091044559057638343023211315200)

theorem momentPanelPhase_owner2622K01P132 :
    (momentPanelPhase2622K01P132 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P132 :
    (momentPanelGrowth2622K01P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P132Input : RatPair2542 := (momentPanelPhase2622K01P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P132Expected : RatState2542 :=
  ((((145209776860542848359172878417317902815562079031548411939647681253181336654282135 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((368163351211070091309339414565925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P132_replay :
    compactExp2620 momentScalarAmp2622K01P132Input 20 = momentScalarAmp2622K01P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K01P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P132_replay] at h
  simpa only [momentPanelPhase_owner2622K01P132] using h

theorem momentScalarAmp2622K01P132_radius_le :
    (momentScalarAmp2622K01P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P132Expected]

def momentScalarGrow2622K01P132Input : RatPair2542 := (momentPanelGrowth2622K01P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P132Expected : RatState2542 :=
  ((((788852333255073701689016314643309878609065040422978345365376455984078124156222861106976126702567 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3999955046531035600967103397055178776258521231019 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P132_replay :
    compactExp2620 momentScalarGrow2622K01P132Input 20 = momentScalarGrow2622K01P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P132] using h

theorem momentScalarGrow2622K01P132_radius_le :
    (momentScalarGrow2622K01P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P132Expected]

end ConnesWeilRH.Dev
