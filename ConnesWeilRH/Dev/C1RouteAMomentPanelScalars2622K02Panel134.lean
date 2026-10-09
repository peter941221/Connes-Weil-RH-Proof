import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P134 : ℚ := ((-108626563163152255396465110601775347522046789634582317 : ℚ) / 3052311915620965801631250374264690298668141930086400)

def momentPanelGrowth2622K02P134 : ℚ := ((6759508666428108141907399971325550009976291349672719 : ℚ) / 14523815245745118345637223853715007457344467920486400)

theorem momentPanelPhase_owner2622K02P134 :
    (momentPanelPhase2622K02P134 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (89 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P134, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P134 :
    (momentPanelGrowth2622K02P134 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P134, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P134Input : RatPair2542 := (momentPanelPhase2622K02P134 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P134Expected : RatState2542 :=
  ((((747825768664810232612293637957082806196570329796393437313285490462065543905939427 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((474006980818557484409587923980593 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P134_replay :
    compactExp2620 momentScalarAmp2622K02P134Input 20 = momentScalarAmp2622K02P134Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P134_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (89 / 200) 0) -
      (momentScalarAmp2622K02P134Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P134]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P134 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P134 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P134Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P134_replay] at h
  simpa only [momentPanelPhase_owner2622K02P134] using h

theorem momentScalarAmp2622K02P134_radius_le :
    (momentScalarAmp2622K02P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P134Expected]

def momentScalarGrow2622K02P134Input : RatPair2542 := (momentPanelGrowth2622K02P134 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P134Expected : RatState2542 :=
  ((((106309732493066838505948893999788051692016977274195628032241094448450901981277478751703803646725 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((4312433164491751271884204538208744179544974669197 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P134_replay :
    compactExp2620 momentScalarGrow2622K02P134Input 20 = momentScalarGrow2622K02P134Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P134_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P134Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P134]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P134 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P134 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P134Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P134_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P134] using h

theorem momentScalarGrow2622K02P134_radius_le :
    (momentScalarGrow2622K02P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P134Expected]

end ConnesWeilRH.Dev
