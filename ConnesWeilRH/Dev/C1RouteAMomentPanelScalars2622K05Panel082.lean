import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P082 : ℚ := ((-19539420902702178300811826878903777797 : ℚ) / 645386273588196152890001535921029120)

def momentPanelGrowth2622K05P082 : ℚ := ((8177923596546570675364616211561567683 : ℚ) / 130362145366030563899357365553174937600)

theorem momentPanelPhase_owner2622K05P082 :
    (momentPanelPhase2622K05P082 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P082, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P082 :
    (momentPanelGrowth2622K05P082 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P082, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P082Input : RatPair2542 := (momentPanelPhase2622K05P082 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P082Expected : RatState2542 :=
  ((((75869402787520471867428150786101495930048731020742970407057229701236988906969757347 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((192357341822671668783044971405756747 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P082_replay :
    compactExp2620 momentScalarAmp2622K05P082Input 20 = momentScalarAmp2622K05P082Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P082_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 40) 0) -
      (momentScalarAmp2622K05P082Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P082]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P082 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P082 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P082Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P082_replay] at h
  simpa only [momentPanelPhase_owner2622K05P082] using h

theorem momentScalarAmp2622K05P082_radius_le :
    (momentScalarAmp2622K05P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P082Expected]

def momentScalarGrow2622K05P082Input : RatPair2542 := (momentPanelGrowth2622K05P082 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P082Expected : RatState2542 :=
  ((((2274274728080828849560513075081168793665036051160940983160732698906889221532609512561630294351767 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2882985551657394014609550087595627521875770810209 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P082_replay :
    compactExp2620 momentScalarGrow2622K05P082Input 20 = momentScalarGrow2622K05P082Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P082_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P082Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P082]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P082 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P082 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P082Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P082_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P082] using h

theorem momentScalarGrow2622K05P082_radius_le :
    (momentScalarGrow2622K05P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P082Expected]

end ConnesWeilRH.Dev
