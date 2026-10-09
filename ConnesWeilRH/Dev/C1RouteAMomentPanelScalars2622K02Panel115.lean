import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P115 : ℚ := ((-331409630007022181830892852689696738817714780385337029 : ℚ) / 10675527291902038718339767394288333721115668198195200)

def momentPanelGrowth2622K02P115 : ℚ := ((56954239062844140016917092116601763937183793094294973 : ℚ) / 258501246680902935909431379014932274757965770968268800)

theorem momentPanelPhase_owner2622K02P115 :
    (momentPanelPhase2622K02P115 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (51 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P115, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P115 :
    (momentPanelGrowth2622K02P115 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P115, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P115Input : RatPair2542 := (momentPanelPhase2622K02P115 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P115Expected : RatState2542 :=
  ((((35187569573698812752342161691292141067418963062892443150827576485986304295860993009 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((89213728582840946256379953604211565 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P115_replay :
    compactExp2620 momentScalarAmp2622K02P115Input 20 = momentScalarAmp2622K02P115Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P115_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (51 / 200) 0) -
      (momentScalarAmp2622K02P115Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P115]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P115 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P115 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P115Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P115_replay] at h
  simpa only [momentPanelPhase_owner2622K02P115] using h

theorem momentScalarAmp2622K02P115_radius_le :
    (momentScalarAmp2622K02P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P115Expected]

def momentScalarGrow2622K02P115Input : RatPair2542 := (momentPanelGrowth2622K02P115 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P115Expected : RatState2542 :=
  ((((2662468408557415323771417145780223612485066489502840390467179868751783010860247946638119106016871 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3375078967031197002411832901218122242855741517981 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P115_replay :
    compactExp2620 momentScalarGrow2622K02P115Input 20 = momentScalarGrow2622K02P115Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P115_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P115Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P115]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P115 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P115 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P115Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P115_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P115] using h

theorem momentScalarGrow2622K02P115_radius_le :
    (momentScalarGrow2622K02P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P115Expected]

end ConnesWeilRH.Dev
