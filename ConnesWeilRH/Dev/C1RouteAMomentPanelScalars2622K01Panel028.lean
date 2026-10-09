import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P028 : ℚ := ((-85838114135655196741074044432423445558646765233171309 : ℚ) / 1774853868264496410090031517308919676848764564275200)

def momentPanelGrowth2622K01P028 : ℚ := ((27705379865976089137180443589250930878803499027747411 : ℚ) / 28170551103130106695367104522054063916003328471859200)

theorem momentPanelPhase_owner2622K01P028 :
    (momentPanelPhase2622K01P028 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P028 :
    (momentPanelGrowth2622K01P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P028Input : RatPair2542 := (momentPanelPhase2622K01P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P028Expected : RatState2542 :=
  ((((529108833370640898744180322053923775739584923110655647759672666115350129033 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5245004138236863824903957 : ℚ) / 5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448))

theorem momentScalarAmp2622K01P028_replay :
    compactExp2620 momentScalarAmp2622K01P028Input 20 = momentScalarAmp2622K01P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K01P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P028_replay] at h
  simpa only [momentPanelPhase_owner2622K01P028] using h

theorem momentScalarAmp2622K01P028_radius_le :
    (momentScalarAmp2622K01P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P028Expected]

def momentScalarGrow2622K01P028Input : RatPair2542 := (momentPanelGrowth2622K01P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P028Expected : RatState2542 :=
  ((((5711125838433226129936086843826953372112309766533070470180052984732121367920474118395888290965737 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7239705306753464396597975732183900394122750644999 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P028_replay :
    compactExp2620 momentScalarGrow2622K01P028Input 20 = momentScalarGrow2622K01P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P028] using h

theorem momentScalarGrow2622K01P028_radius_le :
    (momentScalarGrow2622K01P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P028Expected]

end ConnesWeilRH.Dev
