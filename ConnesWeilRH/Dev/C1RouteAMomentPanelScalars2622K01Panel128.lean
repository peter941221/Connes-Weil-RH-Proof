import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P128 : ℚ := ((-28486851725323081755233007835294665108393936526740503 : ℚ) / 810462602303079318458947687751895813194942670438400)

def momentPanelGrowth2622K01P128 : ℚ := ((839716589212010802921778638669314120439073250738265393 : ℚ) / 2565243694698551426430772497643627026682998695762329600)

theorem momentPanelPhase_owner2622K01P128 :
    (momentPanelPhase2622K01P128 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P128 :
    (momentPanelGrowth2622K01P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P128Input : RatPair2542 := (momentPanelPhase2622K01P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P128Expected : RatState2542 :=
  ((((580235823357874573290806086795019154421814013861506799028138635806486682765283181 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1471121893961741861321700521799637 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P128_replay :
    compactExp2620 momentScalarAmp2622K01P128Input 20 = momentScalarAmp2622K01P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K01P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P128_replay] at h
  simpa only [momentPanelPhase_owner2622K01P128] using h

theorem momentScalarAmp2622K01P128_radius_le :
    (momentScalarAmp2622K01P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P128Expected]

def momentScalarGrow2622K01P128Input : RatPair2542 := (momentPanelGrowth2622K01P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P128Expected : RatState2542 :=
  ((((740802129575083073585772315797124440478235944202581257200603312473149035558775470892538130791483 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3756311884181581916551257054914558246846363334029 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P128_replay :
    compactExp2620 momentScalarGrow2622K01P128Input 20 = momentScalarGrow2622K01P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P128] using h

theorem momentScalarGrow2622K01P128_radius_le :
    (momentScalarGrow2622K01P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P128Expected]

end ConnesWeilRH.Dev
