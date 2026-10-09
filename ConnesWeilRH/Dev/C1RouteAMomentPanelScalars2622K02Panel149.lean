import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P149 : ℚ := ((-108199016009442447671877618853279711945605686892041987 : ℚ) / 2458576875455286491111003410973700321932919334502400)

def momentPanelGrowth2622K02P149 : ℚ := ((131276919716483052217507894586166967638481217679 : ℚ) / 142724769270595988105828596944949513638274662400)

theorem momentPanelPhase_owner2622K02P149 :
    (momentPanelPhase2622K02P149 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P149 :
    (momentPanelGrowth2622K02P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P149Input : RatPair2542 := (momentPanelPhase2622K02P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P149Expected : RatState2542 :=
  ((((41186982666661683023437598275361796579444975083759818329331989958520679470239 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((104426998188612000960623355535 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P149_replay :
    compactExp2620 momentScalarAmp2622K02P149Input 20 = momentScalarAmp2622K02P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K02P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P149_replay] at h
  simpa only [momentPanelPhase_owner2622K02P149] using h

theorem momentScalarAmp2622K02P149_radius_le :
    (momentScalarAmp2622K02P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P149Expected]

def momentScalarGrow2622K02P149Input : RatPair2542 := (momentPanelGrowth2622K02P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P149Expected : RatState2542 :=
  ((((2679345105908492408176437845335310567697810292828318020852587952853444647175424293043823166600629 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6792940904807017462936728577038619269283525528617 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P149_replay :
    compactExp2620 momentScalarGrow2622K02P149Input 20 = momentScalarGrow2622K02P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P149] using h

theorem momentScalarGrow2622K02P149_radius_le :
    (momentScalarGrow2622K02P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P149Expected]

end ConnesWeilRH.Dev
