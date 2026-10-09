import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P131 : ℚ := ((-108834332290421143261098142281820872298009146728220791 : ℚ) / 3150506556879135841448060448962815564051274897817600)

def momentPanelGrowth2622K02P131 : ℚ := ((249529849730802566377119566671221997003977184463944599 : ℚ) / 605078947552075550250886326004771509028706304026214400)

theorem momentPanelPhase_owner2622K02P131 :
    (momentPanelPhase2622K02P131 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (83 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P131 :
    (momentPanelGrowth2622K02P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P131Input : RatPair2542 := (momentPanelPhase2622K02P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P131Expected : RatState2542 :=
  ((((2122678663979174782486992785283223542828145018033578521806382659815003063002010539 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2690903534464055757897567830338253 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P131_replay :
    compactExp2620 momentScalarAmp2622K02P131Input 20 = momentScalarAmp2622K02P131Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622K02P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P131]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P131 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P131_replay] at h
  simpa only [momentPanelPhase_owner2622K02P131] using h

theorem momentScalarAmp2622K02P131_radius_le :
    (momentScalarAmp2622K02P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P131Expected]

def momentScalarGrow2622K02P131Input : RatPair2542 := (momentPanelGrowth2622K02P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P131Expected : RatState2542 :=
  ((((3226251930925635210211169040576044098707831882205332174469011270478504277414883443447160823922313 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4089758588272616176977912624159520327709898452869 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P131_replay :
    compactExp2620 momentScalarGrow2622K02P131Input 20 = momentScalarGrow2622K02P131Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P131_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P131] using h

theorem momentScalarGrow2622K02P131_radius_le :
    (momentScalarGrow2622K02P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P131Expected]

end ConnesWeilRH.Dev
