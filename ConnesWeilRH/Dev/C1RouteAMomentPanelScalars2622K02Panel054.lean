import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P054 : ℚ := ((-119007667139348465773838269060130411203113794180630477 : ℚ) / 3326343472620510098794441280398993364853629281894400)

def momentPanelGrowth2622K02P054 : ℚ := ((13446539485489891143695005951270170362281018149231 : ℚ) / 41247458319202240562584464517090409441461377433600)

theorem momentPanelPhase_owner2622K02P054 :
    (momentPanelPhase2622K02P054 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P054 :
    (momentPanelGrowth2622K02P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P054Input : RatPair2542 := (momentPanelPhase2622K02P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P054Expected : RatState2542 :=
  ((((38688720933586851742393527647135300194728488192492865882475899254565451930165443 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((392363630902313755980881256498909 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P054_replay :
    compactExp2620 momentScalarAmp2622K02P054Input 20 = momentScalarAmp2622K02P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K02P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P054_replay] at h
  simpa only [momentPanelPhase_owner2622K02P054] using h

theorem momentScalarAmp2622K02P054_radius_le :
    (momentScalarAmp2622K02P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P054Expected]

def momentScalarGrow2622K02P054Input : RatPair2542 := (momentPanelGrowth2622K02P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P054Expected : RatState2542 :=
  ((((1479609901221963754709452388475133327751623889532755574329406405643226063488948763029870186110117 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3751255592529355382905429192909576085353631891651 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P054_replay :
    compactExp2620 momentScalarGrow2622K02P054Input 20 = momentScalarGrow2622K02P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P054] using h

theorem momentScalarGrow2622K02P054_radius_le :
    (momentScalarGrow2622K02P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P054Expected]

end ConnesWeilRH.Dev
