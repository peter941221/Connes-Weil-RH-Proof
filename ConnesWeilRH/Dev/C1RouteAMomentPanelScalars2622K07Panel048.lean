import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P048 : ℚ := ((-35452025672836053999102337082937231325 : ℚ) / 895427819182013945876423249775034368)

def momentPanelGrowth2622K07P048 : ℚ := ((77774065377625744917782554905966747075 : ℚ) / 171973780297797574761172633658580795392)

theorem momentPanelPhase_owner2622K07P048 :
    (momentPanelPhase2622K07P048 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P048 :
    (momentPanelGrowth2622K07P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P048Input : RatPair2542 := (momentPanelPhase2622K07P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P048Expected : RatState2542 :=
  ((((426325673945243028666011767513776610181149046374646959358146324158091942060503 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((17294479299773141137256878694803 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P048_replay :
    compactExp2620 momentScalarAmp2622K07P048Input 20 = momentScalarAmp2622K07P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K07P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P048_replay] at h
  simpa only [momentPanelPhase_owner2622K07P048] using h

theorem momentScalarAmp2622K07P048_radius_le :
    (momentScalarAmp2622K07P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P048Expected]

def momentScalarGrow2622K07P048Input : RatPair2542 := (momentPanelGrowth2622K07P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P048Expected : RatState2542 :=
  ((((3357419223348929948062427672527885924330810509554677475970441982987066630442555361095771611381335 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1064008164524390754198232715968578197646568796847 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P048_replay :
    compactExp2620 momentScalarGrow2622K07P048Input 20 = momentScalarGrow2622K07P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P048] using h

theorem momentScalarGrow2622K07P048_radius_le :
    (momentScalarGrow2622K07P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P048Expected]

end ConnesWeilRH.Dev
