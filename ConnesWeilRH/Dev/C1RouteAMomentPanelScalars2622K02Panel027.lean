import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P027 : ℚ := ((-7686798005013153899032440318245210819156852264015 : ℚ) / 148433760041419827630061740822747494183805648896)

def momentPanelGrowth2622K02P027 : ℚ := ((5607240797980157143684333226779956382718057642724537519 : ℚ) / 5191322466413386322129767429363367806533932402763366400)

theorem momentPanelPhase_owner2622K02P027 :
    (momentPanelPhase2622K02P027 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-5 / 8) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P027 :
    (momentPanelGrowth2622K02P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P027Input : RatPair2542 := (momentPanelPhase2622K02P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P027Expected : RatState2542 :=
  ((((69056281970470558718710255944005792493660000838904163419881179283155198251 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((89961412337922103381840805 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P027_replay :
    compactExp2620 momentScalarAmp2622K02P027Input 20 = momentScalarAmp2622K02P027Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622K02P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P027]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P027 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P027_replay] at h
  simpa only [momentPanelPhase_owner2622K02P027] using h

theorem momentScalarAmp2622K02P027_radius_le :
    (momentScalarAmp2622K02P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P027Expected]

def momentScalarGrow2622K02P027Input : RatPair2542 := (momentPanelGrowth2622K02P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P027Expected : RatState2542 :=
  ((((6290539535247928902188796064562644768553894781366230611052706454379041391212067483389052467540143 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7974198003544053819565998424694493104776586656735 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P027_replay :
    compactExp2620 momentScalarGrow2622K02P027Input 20 = momentScalarGrow2622K02P027Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P027_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P027] using h

theorem momentScalarGrow2622K02P027_radius_le :
    (momentScalarGrow2622K02P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P027Expected]

end ConnesWeilRH.Dev
