import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P010 : ℚ := ((-2467382113981525588946430812021548549569 : ℚ) / 29853678695614893697007959167886950400)

def momentPanelGrowth2622K05P010 : ℚ := ((101798452260099440896858940778889403 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K05P010 :
    (momentPanelPhase2622K05P010 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P010 :
    (momentPanelGrowth2622K05P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P010Input : RatPair2542 := (momentPanelPhase2622K05P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P010Expected : RatState2542 :=
  ((((2725932390438023141519593490440315430450391705172864625996035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639232714157083089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P010_replay :
    compactExp2620 momentScalarAmp2622K05P010Input 20 = momentScalarAmp2622K05P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K05P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P010_replay] at h
  simpa only [momentPanelPhase_owner2622K05P010] using h

theorem momentScalarAmp2622K05P010_radius_le :
    (momentScalarAmp2622K05P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P010Expected]

def momentScalarGrow2622K05P010Input : RatPair2542 := (momentPanelGrowth2622K05P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P010Expected : RatState2542 :=
  ((((43973948318536051246394379624588631030003081177988310087430399679289578283124767622231773739668989 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3483962771065576381454898365809518782004902002019 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P010_replay :
    compactExp2620 momentScalarGrow2622K05P010Input 20 = momentScalarGrow2622K05P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P010] using h

theorem momentScalarGrow2622K05P010_radius_le :
    (momentScalarGrow2622K05P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P010Expected]

end ConnesWeilRH.Dev
