import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P045 : ℚ := ((-35568636791352857102036424601602537775 : ℚ) / 867519223567389247373071832005476352)

def momentPanelGrowth2622K07P045 : ℚ := ((2085671661737428735056377229611480475 : ℚ) / 4127916567354395268022592476232548352)

theorem momentPanelPhase_owner2622K07P045 :
    (momentPanelPhase2622K07P045 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P045 :
    (momentPanelGrowth2622K07P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P045Input : RatPair2542 := (momentPanelPhase2622K07P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P045Expected : RatState2542 :=
  ((((3336954822266015276445450674412176722658402528086186057783465153039083998814787 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4230260605451118880292805551605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P045_replay :
    compactExp2620 momentScalarAmp2622K07P045Input 20 = momentScalarAmp2622K07P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K07P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P045_replay] at h
  simpa only [momentPanelPhase_owner2622K07P045] using h

theorem momentScalarAmp2622K07P045_radius_le :
    (momentScalarAmp2622K07P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P045Expected]

def momentScalarGrow2622K07P045Input : RatPair2542 := (momentPanelGrowth2622K07P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P045Expected : RatState2542 :=
  ((((3540220388419823838408247215883479770866765703075052133947031254205681359442297937512873210038677 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4487760337876568402353067434878385442981970757747 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P045_replay :
    compactExp2620 momentScalarGrow2622K07P045Input 20 = momentScalarGrow2622K07P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P045] using h

theorem momentScalarGrow2622K07P045_radius_le :
    (momentScalarGrow2622K07P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P045Expected]

end ConnesWeilRH.Dev
