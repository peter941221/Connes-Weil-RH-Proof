import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P169 : ℚ := ((-218592406341900690166257117348954048236123622780715575 : ℚ) / 2688980324984195006630004631593871220789458887507968)

def momentPanelGrowth2622K03P169 : ℚ := ((9141686223207495248277701317575863794969744381075 : ℚ) / 2466284012995898674468718155208727595669386166272)

theorem momentPanelPhase_owner2622K03P169 :
    (momentPanelPhase2622K03P169 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (159 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P169, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P169 :
    (momentPanelGrowth2622K03P169 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P169, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P169Input : RatPair2542 := (momentPanelPhase2622K03P169 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P169Expected : RatState2542 :=
  ((((2647896655939520785171369281377131153022510986972875571380341 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639242685832259697 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P169_replay :
    compactExp2620 momentScalarAmp2622K03P169Input 20 = momentScalarAmp2622K03P169Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P169_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (159 / 200) 0) -
      (momentScalarAmp2622K03P169Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P169]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P169 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P169 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P169Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P169_replay] at h
  simpa only [momentPanelPhase_owner2622K03P169] using h

theorem momentScalarAmp2622K03P169_radius_le :
    (momentScalarAmp2622K03P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P169Expected]

def momentScalarGrow2622K03P169Input : RatPair2542 := (momentPanelGrowth2622K03P169 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P169Expected : RatState2542 :=
  ((((43486289082190977456735808689472223090218894629076283028929482122557625696111876373669776962483277 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((110250451182923382846170052461231747039667740437011 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P169_replay :
    compactExp2620 momentScalarGrow2622K03P169Input 20 = momentScalarGrow2622K03P169Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P169_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P169Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P169]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P169 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P169 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P169Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P169_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P169] using h

theorem momentScalarGrow2622K03P169_radius_le :
    (momentScalarGrow2622K03P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P169Expected]

end ConnesWeilRH.Dev
