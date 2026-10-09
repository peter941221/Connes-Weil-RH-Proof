import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P148 : ℚ := ((-87273721709009623561207636529515098975 : ℚ) / 2134601916326716402097904514345467904)

def momentPanelGrowth2622K07P148 : ℚ := ((525058403318110800904873122507795256025 : ℚ) / 574632588584167970839672921906357469184)

theorem momentPanelPhase_owner2622K07P148 :
    (momentPanelPhase2622K07P148 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (117 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P148 :
    (momentPanelGrowth2622K07P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P148Input : RatPair2542 := (momentPanelPhase2622K07P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P148Expected : RatState2542 :=
  ((((3744229350620087763649563722647231013902656823926063800805545686948282033571033 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4746562072043083795833423943563 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P148_replay :
    compactExp2620 momentScalarAmp2622K07P148Input 20 = momentScalarAmp2622K07P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K07P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P148_replay] at h
  simpa only [momentPanelPhase_owner2622K07P148] using h

theorem momentScalarAmp2622K07P148_radius_le :
    (momentScalarAmp2622K07P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P148Expected]

def momentScalarGrow2622K07P148Input : RatPair2542 := (momentPanelGrowth2622K07P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P148Expected : RatState2542 :=
  ((((5326305001015655165119310532311690653367592804468792562448649915459748461301145315152008300770989 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6751887847939936277274883061567737203213204664437 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P148_replay :
    compactExp2620 momentScalarGrow2622K07P148Input 20 = momentScalarGrow2622K07P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P148] using h

theorem momentScalarGrow2622K07P148_radius_le :
    (momentScalarGrow2622K07P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P148Expected]

end ConnesWeilRH.Dev
