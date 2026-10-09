import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P030 : ℚ := ((-120160614823511133297448136258639509875633772947958013 : ℚ) / 2458576875455286491111003410973700321932919334502400)

def momentPanelGrowth2622K02P030 : ℚ := ((131276919716483052217507894586166967638481217679 : ℚ) / 142724769270595988105828596944949513638274662400)

theorem momentPanelPhase_owner2622K02P030 :
    (momentPanelPhase2622K02P030 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P030 :
    (momentPanelGrowth2622K02P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P030Input : RatPair2542 := (momentPanelPhase2622K02P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P030Expected : RatState2542 :=
  ((((1270186185979141496595185589020201491067896217882352430991644183167579219167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((806322591764516849773741327 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P030_replay :
    compactExp2620 momentScalarAmp2622K02P030Input 20 = momentScalarAmp2622K02P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K02P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P030_replay] at h
  simpa only [momentPanelPhase_owner2622K02P030] using h

theorem momentScalarAmp2622K02P030_radius_le :
    (momentScalarAmp2622K02P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P030Expected]

def momentScalarGrow2622K02P030Input : RatPair2542 := (momentPanelGrowth2622K02P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P030Expected : RatState2542 :=
  ((((2679345105908492408176437845335310567697810292828318020852587952853444647175424293043823166600629 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6792940904807017462936728577038619269283525528617 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P030_replay :
    compactExp2620 momentScalarGrow2622K02P030Input 20 = momentScalarGrow2622K02P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P030] using h

theorem momentScalarGrow2622K02P030_radius_le :
    (momentScalarGrow2622K02P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P030Expected]

end ConnesWeilRH.Dev
