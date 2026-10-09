import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P001 : ℚ := ((-2457995274203066295629255185635386284023 : ℚ) / 17586877367326363424604661590104473600)

def momentPanelGrowth2622K16P001 : ℚ := ((18073973925269168202087872797630754290643 : ℚ) / 1461091039461616660414536522428684697600)

theorem momentPanelPhase_owner2622K16P001 :
    (momentPanelPhase2622K16P001 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-177 / 200) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P001, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P001 :
    (momentPanelGrowth2622K16P001 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (-177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P001, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P001Input : RatPair2542 := (momentPanelPhase2622K16P001 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P001Expected : RatState2542 :=
  ((((213922166180321291872444315292682757 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K16P001_replay :
    compactExp2620 momentScalarAmp2622K16P001Input 20 = momentScalarAmp2622K16P001Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P001_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-177 / 200) 0) -
      (momentScalarAmp2622K16P001Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P001]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P001 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P001 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P001Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P001_replay] at h
  simpa only [momentPanelPhase_owner2622K16P001] using h

theorem momentScalarAmp2622K16P001_radius_le :
    (momentScalarAmp2622K16P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P001Expected]

def momentScalarGrow2622K16P001Input : RatPair2542 := (momentPanelGrowth2622K16P001 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P001Expected : RatState2542 :=
  ((((503389227084758867104552609270843655138370333169646597090375388516237778409766480540537424062851411301 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((319057063950518246321644279820185434851080781469547965 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K16P001_replay :
    compactExp2620 momentScalarGrow2622K16P001Input 20 = momentScalarGrow2622K16P001Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P001_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P001Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P001]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P001 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P001 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P001Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P001_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P001] using h

theorem momentScalarGrow2622K16P001_radius_le :
    (momentScalarGrow2622K16P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P001Expected]

end ConnesWeilRH.Dev
