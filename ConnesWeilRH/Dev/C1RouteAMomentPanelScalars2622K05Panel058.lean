import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P058 : ℚ := ((-2466375058659678413573520847123140398817 : ℚ) / 73079550042917333704524341108644249600)

def momentPanelGrowth2622K05P058 : ℚ := ((26854364219335813968512191773466223723 : ℚ) / 106388337214514289458251714533104025600)

theorem momentPanelPhase_owner2622K05P058 :
    (momentPanelPhase2622K05P058 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-63 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P058 :
    (momentPanelGrowth2622K05P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P058Input : RatPair2542 := (momentPanelPhase2622K05P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P058Expected : RatState2542 :=
  ((((2352258053548859098167615368091202211669723045938043215870189256253672180850033261 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2981937308961558376056471170894075 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P058_replay :
    compactExp2620 momentScalarAmp2622K05P058Input 20 = momentScalarAmp2622K05P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K05P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P058_replay] at h
  simpa only [momentPanelPhase_owner2622K05P058] using h

theorem momentScalarAmp2622K05P058_radius_le :
    (momentScalarAmp2622K05P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P058Expected]

def momentScalarGrow2622K05P058Input : RatPair2542 := (momentPanelGrowth2622K05P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P058Expected : RatState2542 :=
  ((((2749302274579913063012022778918614079705752084854598544806446264795235679693552089242458600552929 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3485153839616796778541785664755148499665115483443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P058_replay :
    compactExp2620 momentScalarGrow2622K05P058Input 20 = momentScalarGrow2622K05P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P058] using h

theorem momentScalarGrow2622K05P058_radius_le :
    (momentScalarGrow2622K05P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P058Expected]

end ConnesWeilRH.Dev
