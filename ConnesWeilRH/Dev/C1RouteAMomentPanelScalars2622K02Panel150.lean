import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P150 : ℚ := ((-108211468385940560537774571322111289485118793392008973 : ℚ) / 2412904949288695774917138259951316477568671442534400)

def momentPanelGrowth2622K02P150 : ℚ := ((1817928441878330513014753122139698007657640397644401013 : ℚ) / 1875681353341401134099429812134888425909982784703692800)

theorem momentPanelPhase_owner2622K02P150 :
    (momentPanelPhase2622K02P150 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P150 :
    (momentPanelGrowth2622K02P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P150Input : RatPair2542 := (momentPanelPhase2622K02P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P150Expected : RatState2542 :=
  ((((8906731740095346733720316417650991195721767799275263907136112474365495382793 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((45165635885592441835181731161 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P150_replay :
    compactExp2620 momentScalarAmp2622K02P150Input 20 = momentScalarAmp2622K02P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K02P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P150_replay] at h
  simpa only [momentPanelPhase_owner2622K02P150] using h

theorem momentScalarAmp2622K02P150_radius_le :
    (momentScalarAmp2622K02P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P150Expected]

def momentScalarGrow2622K02P150Input : RatPair2542 := (momentPanelGrowth2622K02P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P150Expected : RatState2542 :=
  ((((5630163529580272935352413922185749916631258449559361032786955073726839412753347442069993835602839 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7137073580781583260367013617698691836853333566057 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P150_replay :
    compactExp2620 momentScalarGrow2622K02P150Input 20 = momentScalarGrow2622K02P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P150] using h

theorem momentScalarGrow2622K02P150_radius_le :
    (momentScalarGrow2622K02P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P150Expected]

end ConnesWeilRH.Dev
