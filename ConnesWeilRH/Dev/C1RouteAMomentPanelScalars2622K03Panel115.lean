import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P115 : ℚ := ((-218709485015766338990674023318611134407242604555864675 : ℚ) / 6832337466817304779737451132344533581514027646844928)

def momentPanelGrowth2622K03P115 : ℚ := ((30176509711051587675595191102349885307503984385010475 : ℚ) / 165440797875777878982036082569556655845098093419692032)

theorem momentPanelPhase_owner2622K03P115 :
    (momentPanelPhase2622K03P115 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (51 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P115, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P115 :
    (momentPanelGrowth2622K03P115 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P115, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P115Input : RatPair2542 := (momentPanelPhase2622K03P115 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P115Expected : RatState2542 :=
  ((((26756407669011072650839908033091272574690022874600844350380388023714581824290771111 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((33918811701770596443065732485111139 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P115_replay :
    compactExp2620 momentScalarAmp2622K03P115Input 20 = momentScalarAmp2622K03P115Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P115_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (51 / 200) 0) -
      (momentScalarAmp2622K03P115Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P115]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P115 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P115 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P115Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P115_replay] at h
  simpa only [momentPanelPhase_owner2622K03P115] using h

theorem momentScalarAmp2622K03P115_radius_le :
    (momentScalarAmp2622K03P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P115Expected]

def momentScalarGrow2622K03P115Input : RatPair2542 := (momentPanelGrowth2622K03P115 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P115Expected : RatState2542 :=
  ((((1281693595772544969106171556559070159823353772352983037878929016000206893280884446635701127689371 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1624739373364975206509049275356603067959776522065 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P115_replay :
    compactExp2620 momentScalarGrow2622K03P115Input 20 = momentScalarGrow2622K03P115Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P115_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P115Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P115]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P115 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P115 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P115Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P115_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P115] using h

theorem momentScalarGrow2622K03P115_radius_le :
    (momentScalarGrow2622K03P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P115Expected]

end ConnesWeilRH.Dev
