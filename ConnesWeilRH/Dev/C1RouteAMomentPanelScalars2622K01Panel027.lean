import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P027 : ℚ := ((-1831195726912033752090539655829550139820896236465 : ℚ) / 37108440010354956907515435205686873545951412224)

def momentPanelGrowth2622K01P027 : ℚ := ((1351165734041696844095647076123473549414244344889494353 : ℚ) / 1297830616603346580532441857340841951633483100690841600)

theorem momentPanelPhase_owner2622K01P027 :
    (momentPanelPhase2622K01P027 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-5 / 8) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P027 :
    (momentPanelGrowth2622K01P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P027Input : RatPair2542 := (momentPanelPhase2622K01P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P027Expected : RatState2542 :=
  ((((395707250829963779002651604794295001461699388861591342395034244296876502121 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((502851067128826006355618541 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P027_replay :
    compactExp2620 momentScalarAmp2622K01P027Input 20 = momentScalarAmp2622K01P027Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622K01P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P027]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P027 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P027_replay] at h
  simpa only [momentPanelPhase_owner2622K01P027] using h

theorem momentScalarAmp2622K01P027_radius_le :
    (momentScalarAmp2622K01P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P027Expected]

def momentScalarGrow2622K01P027Input : RatPair2542 := (momentPanelGrowth2622K01P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P027Expected : RatState2542 :=
  ((((6049795342004506832762661998768159256869813312403875968648954809671187690918778951099459295847159 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7669019082236905804396979431229561607700069786097 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P027_replay :
    compactExp2620 momentScalarGrow2622K01P027Input 20 = momentScalarGrow2622K01P027Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P027_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P027] using h

theorem momentScalarGrow2622K01P027_radius_le :
    (momentScalarGrow2622K01P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P027Expected]

end ConnesWeilRH.Dev
