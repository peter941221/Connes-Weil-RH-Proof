import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K12
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K12P043 : ℚ := ((-2479684276506465370695837432777795567267 : ℚ) / 63587382348408351946117027506788761600)

def momentPanelGrowth2622K12P043 : ℚ := ((9850529699711404398462521954912623915763 : ℚ) / 20518929880883213830845548564800182681600)

theorem momentPanelPhase_owner2622K12P043 :
    (momentPanelPhase2622K12P043 : ℝ) = momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (-93 / 200) 0 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P043, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K12P043 :
    (momentPanelGrowth2622K12P043 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2))
      (-93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P043, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K12P043Input : RatPair2542 := (momentPanelPhase2622K12P043 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K12P043Expected : RatState2542 :=
  ((((24753762514472805654568610451204184933787777124582094110935106186307392734971371 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((31380291336726313716147283129103 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K12P043_replay :
    compactExp2620 momentScalarAmp2622K12P043Input 20 = momentScalarAmp2622K12P043Expected := by
  decide +kernel

theorem momentScalarAmp2622K12P043_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (-93 / 200) 0) -
      (momentScalarAmp2622K12P043Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K12P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K12P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P043]
  have h := compactExp_real_error2620 momentPanelPhase2622K12P043 20 hsmall
  change |Real.exp (momentPanelPhase2622K12P043 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K12P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K12P043Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K12P043_replay] at h
  simpa only [momentPanelPhase_owner2622K12P043] using h

theorem momentScalarAmp2622K12P043_radius_le :
    (momentScalarAmp2622K12P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarAmp2622K12P043Expected]

def momentScalarGrow2622K12P043Input : RatPair2542 := (momentPanelGrowth2622K12P043 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K12P043Expected : RatState2542 :=
  ((((431519599706256016443980901475389211602641414332231563830957479845071523143726737421258395900697 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4376126633097222885467248338317722585342013051851 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K12P043_replay :
    compactExp2620 momentScalarGrow2622K12P043Input 20 = momentScalarGrow2622K12P043Expected := by
  decide +kernel

theorem momentScalarGrow2622K12P043_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (-93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K12P043Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K12P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K12P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P043]
  have h := compactExp_real_error2620 momentPanelGrowth2622K12P043 20 hsmall
  change |Real.exp (momentPanelGrowth2622K12P043 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K12P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K12P043Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K12P043_replay] at h
  simpa only [momentPanelGrowth_owner2622K12P043] using h

theorem momentScalarGrow2622K12P043_radius_le :
    (momentScalarGrow2622K12P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarGrow2622K12P043Expected]

end ConnesWeilRH.Dev
