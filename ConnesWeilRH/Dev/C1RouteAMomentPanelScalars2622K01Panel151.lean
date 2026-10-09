import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P151 : ℚ := ((-85431608989059988985920271901515970807282829646828691 : ℚ) / 1774853868264496410090031517308919676848764564275200)

def momentPanelGrowth2622K01P151 : ℚ := ((27705379865976089137180443589250930878803499027747411 : ℚ) / 28170551103130106695367104522054063916003328471859200)

theorem momentPanelPhase_owner2622K01P151 :
    (momentPanelPhase2622K01P151 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (123 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P151, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P151 :
    (momentPanelGrowth2622K01P151 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P151, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P151Input : RatPair2542 := (momentPanelPhase2622K01P151 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P151Expected : RatState2542 :=
  ((((2661178492561479027503512541680673512043518750225625983884780018264978557015 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3376017225176173942896469247 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P151_replay :
    compactExp2620 momentScalarAmp2622K01P151Input 20 = momentScalarAmp2622K01P151Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P151_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (123 / 200) 0) -
      (momentScalarAmp2622K01P151Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P151]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P151 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P151 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P151Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P151_replay] at h
  simpa only [momentPanelPhase_owner2622K01P151] using h

theorem momentScalarAmp2622K01P151_radius_le :
    (momentScalarAmp2622K01P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P151Expected]

def momentScalarGrow2622K01P151Input : RatPair2542 := (momentPanelGrowth2622K01P151 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P151Expected : RatState2542 :=
  ((((5711125838433226129936086843826953372112309766533070470180052984732121367920474118395888290965737 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7239705306753464396597975732183900394122750644999 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P151_replay :
    compactExp2620 momentScalarGrow2622K01P151Input 20 = momentScalarGrow2622K01P151Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P151_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P151Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P151]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P151 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P151 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P151Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P151_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P151] using h

theorem momentScalarGrow2622K01P151_radius_le :
    (momentScalarGrow2622K01P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P151Expected]

end ConnesWeilRH.Dev
