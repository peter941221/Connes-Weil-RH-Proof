import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P009 : ℚ := ((-822109592006088926979998124828898038997 : ℚ) / 9518534826993728929958445028527308800)

def momentPanelGrowth2622K05P009 : ℚ := ((49455510713224339993275567682960935239169 : ℚ) / 11993719979505444364398792983830121676800)

theorem momentPanelPhase_owner2622K05P009 :
    (momentPanelPhase2622K05P009 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-161 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P009 :
    (momentPanelGrowth2622K05P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P009Input : RatPair2542 := (momentPanelPhase2622K05P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P009Expected : RatState2542 :=
  ((((16512387996049644617148624926719305590839241628496765573993 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208925819614671042456853 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P009_replay :
    compactExp2620 momentScalarAmp2622K05P009Input 20 = momentScalarAmp2622K05P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K05P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P009_replay] at h
  simpa only [momentPanelPhase_owner2622K05P009] using h

theorem momentScalarAmp2622K05P009_radius_le :
    (momentScalarAmp2622K05P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P009Expected]

def momentScalarGrow2622K05P009Input : RatPair2542 := (momentPanelGrowth2622K05P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P009Expected : RatState2542 :=
  ((((131944233169518391438932584719212050297394427644938734769645157571373467374697061093872101364655201 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((167258528640438083230751266599631264929327617239903 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P009_replay :
    compactExp2620 momentScalarGrow2622K05P009Input 20 = momentScalarGrow2622K05P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P009] using h

theorem momentScalarGrow2622K05P009_radius_le :
    (momentScalarGrow2622K05P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P009Expected]

end ConnesWeilRH.Dev
