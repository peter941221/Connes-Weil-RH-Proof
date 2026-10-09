import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P161 : ℚ := ((-108741785574741635269942722340082906142115112478231851 : ℚ) / 1860274642672948108971369932580471960761271949721600)

def momentPanelGrowth2622K02P161 : ℚ := ((24613482304153243453556696928747838981954145439095079 : ℚ) / 12931006820685267118376176711809370885141322688102400)

theorem momentPanelPhase_owner2622K02P161 :
    (momentPanelPhase2622K02P161 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (143 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P161, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P161 :
    (momentPanelGrowth2622K02P161 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P161, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P161Input : RatPair2542 := (momentPanelPhase2622K02P161 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P161Expected : RatState2542 :=
  ((((87709660749817031602817957494675279009803217444587575246729513693477747 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2529043041711062099607661 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P161_replay :
    compactExp2620 momentScalarAmp2622K02P161Input 20 = momentScalarAmp2622K02P161Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P161_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (143 / 200) 0) -
      (momentScalarAmp2622K02P161Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P161]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P161 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P161 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P161Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P161_replay] at h
  simpa only [momentPanelPhase_owner2622K02P161] using h

theorem momentScalarAmp2622K02P161_radius_le :
    (momentScalarAmp2622K02P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P161Expected]

def momentScalarGrow2622K02P161Input : RatPair2542 := (momentPanelGrowth2622K02P161 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P161Expected : RatState2542 :=
  ((((3582572773097152492556085762090111323437650676260990655767705359873574340982035858747343206666053 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2270721141117262665851674846476261911870756881715 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P161_replay :
    compactExp2620 momentScalarGrow2622K02P161Input 20 = momentScalarGrow2622K02P161Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P161_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P161Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P161]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P161 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P161 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P161Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P161_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P161] using h

theorem momentScalarGrow2622K02P161_radius_le :
    (momentScalarGrow2622K02P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P161Expected]

end ConnesWeilRH.Dev
