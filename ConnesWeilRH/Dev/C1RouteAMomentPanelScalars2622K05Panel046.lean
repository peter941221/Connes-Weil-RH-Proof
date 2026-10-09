import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P046 : ℚ := ((-2474268352776789579073126544029797190233 : ℚ) / 65777882585602732351903330645678489600)

def momentPanelGrowth2622K05P046 : ℚ := ((563627425135780671034626191651660747 : ℚ) / 1341681395281557998544110672569958400)

theorem momentPanelPhase_owner2622K05P046 :
    (momentPanelPhase2622K05P046 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P046 :
    (momentPanelGrowth2622K05P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P046Input : RatPair2542 := (momentPanelPhase2622K05P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P046Expected : RatState2542 :=
  ((((3077810242794005594158681899892352805614268136818306428148305648022347245877547 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((7803456082351178789981273687793 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K05P046_replay :
    compactExp2620 momentScalarAmp2622K05P046Input 20 = momentScalarAmp2622K05P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K05P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P046_replay] at h
  simpa only [momentPanelPhase_owner2622K05P046] using h

theorem momentScalarAmp2622K05P046_radius_le :
    (momentScalarAmp2622K05P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P046Expected]

def momentScalarGrow2622K05P046Input : RatPair2542 := (momentPanelGrowth2622K05P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P046Expected : RatState2542 :=
  ((((3251183927276683428608811405464136116238946068502644755730617962563602463893114234123829903129361 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4121363605724940622186307772359895753301710255645 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P046_replay :
    compactExp2620 momentScalarGrow2622K05P046Input 20 = momentScalarGrow2622K05P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P046] using h

theorem momentScalarGrow2622K05P046_radius_le :
    (momentScalarGrow2622K05P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P046Expected]

end ConnesWeilRH.Dev
