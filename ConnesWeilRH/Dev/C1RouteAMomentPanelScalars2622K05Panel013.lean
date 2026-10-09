import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P013 : ℚ := ((-2470217204837718306314044071831468562647 : ℚ) / 33650545773418486400370884608629145600)

def momentPanelGrowth2622K05P013 : ℚ := ((15696515806448900791722026820391289593883 : ℚ) / 5602353432335214727576086290007431577600)

theorem momentPanelPhase_owner2622K05P013 :
    (momentPanelPhase2622K05P013 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P013 :
    (momentPanelGrowth2622K05P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P013Input : RatPair2542 := (momentPanelPhase2622K05P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P013Expected : RatState2542 :=
  ((((28114855921278736781029237781840432880381304189608357768357671347 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851674871568021411475 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P013_replay :
    compactExp2620 momentScalarAmp2622K05P013Input 20 = momentScalarAmp2622K05P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K05P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P013_replay] at h
  simpa only [momentPanelPhase_owner2622K05P013] using h

theorem momentScalarAmp2622K05P013_radius_le :
    (momentScalarAmp2622K05P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P013Expected]

def momentScalarGrow2622K05P013Input : RatPair2542 := (momentPanelGrowth2622K05P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P013Expected : RatState2542 :=
  ((((35187842595368202514691366140009513998112067794067355256275771252903864655245777233770465098556011 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22302885300483534652349846415927801786486129351447 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P013_replay :
    compactExp2620 momentScalarGrow2622K05P013Input 20 = momentScalarGrow2622K05P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P013] using h

theorem momentScalarGrow2622K05P013_radius_le :
    (momentScalarGrow2622K05P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P013Expected]

end ConnesWeilRH.Dev
