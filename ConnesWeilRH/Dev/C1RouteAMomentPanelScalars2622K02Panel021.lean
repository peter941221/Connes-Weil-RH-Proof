import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P021 : ℚ := ((-119837354864166027137673359844238510562631395307296771 : ℚ) / 2020126384256015615649897961158815416036139571609600)

def momentPanelGrowth2622K02P021 : ℚ := ((6068965656088175361156949622644170102627624064822212159 : ℚ) / 3917384011867129827655238305608259639720874890126950400)

theorem momentPanelPhase_owner2622K02P021 :
    (momentPanelPhase2622K02P021 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-137 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P021 :
    (momentPanelGrowth2622K02P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P021Input : RatPair2542 := (momentPanelPhase2622K02P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P021Expected : RatState2542 :=
  ((((4606982883077115759189393852870194897390944967443322280059234408254443 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2464574639378901008195061 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P021_replay :
    compactExp2620 momentScalarAmp2622K02P021Input 20 = momentScalarAmp2622K02P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K02P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P021_replay] at h
  simpa only [momentPanelPhase_owner2622K02P021] using h

theorem momentScalarAmp2622K02P021_radius_le :
    (momentScalarAmp2622K02P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P021Expected]

def momentScalarGrow2622K02P021Input : RatPair2542 := (momentPanelGrowth2622K02P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P021Expected : RatState2542 :=
  ((((10055987736307356911312324390541034225067599215168055063398768790892477015442664976535618295070367 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6373730027908117235947057885882021998267208100801 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P021_replay :
    compactExp2620 momentScalarGrow2622K02P021Input 20 = momentScalarGrow2622K02P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P021] using h

theorem momentScalarGrow2622K02P021_radius_le :
    (momentScalarGrow2622K02P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P021Expected]

end ConnesWeilRH.Dev
