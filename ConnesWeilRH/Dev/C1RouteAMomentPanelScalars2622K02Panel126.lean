import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P126 : ℚ := ((-109256861148072667450225756278116340731066335885957181 : ℚ) / 3298940316920555669078122189785563058235080546713600)

def momentPanelGrowth2622K02P126 : ℚ := ((1201060096676611503532489102941988961447009012020410773 : ℚ) / 3544053980243876701303226846407059068613776154348748800)

theorem momentPanelPhase_owner2622K02P126 :
    (momentPanelPhase2622K02P126 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (73 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P126 :
    (momentPanelGrowth2622K02P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P126Input : RatPair2542 := (momentPanelPhase2622K02P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P126Expected : RatState2542 :=
  ((((8836850488269061391083291572293571271237621551883041451335666432109759342864103225 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11202392644660272261327874038031395 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P126_replay :
    compactExp2620 momentScalarAmp2622K02P126Input 20 = momentScalarAmp2622K02P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K02P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P126_replay] at h
  simpa only [momentPanelPhase_owner2622K02P126] using h

theorem momentScalarAmp2622K02P126_radius_le :
    (momentScalarAmp2622K02P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P126Expected]

def momentScalarGrow2622K02P126Input : RatPair2542 := (momentPanelGrowth2622K02P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P126Expected : RatState2542 :=
  ((((2997633864727658309814796053529973334595656180014813385208082800974996293338482572331422922411819 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3799951139761461510423881606343925188755009186119 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P126_replay :
    compactExp2620 momentScalarGrow2622K02P126Input 20 = momentScalarGrow2622K02P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P126] using h

theorem momentScalarGrow2622K02P126_radius_le :
    (momentScalarGrow2622K02P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P126Expected]

end ConnesWeilRH.Dev
