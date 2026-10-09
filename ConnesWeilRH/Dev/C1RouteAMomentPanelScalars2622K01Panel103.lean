import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P103 : ℚ := ((-85564412791819928940202325508720749915059813562361459 : ℚ) / 2802472207012787524451997415312556175044342133555200)

def momentPanelGrowth2622K01P103 : ℚ := ((6377255035296005619080216163979008805290443934245491 : ℚ) / 71450410136745634128578568259640554431673737098035200)

theorem momentPanelPhase_owner2622K01P103 :
    (momentPanelPhase2622K01P103 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P103 :
    (momentPanelGrowth2622K01P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P103Input : RatPair2542 := (momentPanelPhase2622K01P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P103Expected : RatState2542 :=
  ((((117441910592155752820596958308480496767433540978649043852394413185869437849784886891 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((148879643375083784491018159074262667 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P103_replay :
    compactExp2620 momentScalarAmp2622K01P103Input 20 = momentScalarAmp2622K01P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K01P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P103_replay] at h
  simpa only [momentPanelPhase_owner2622K01P103] using h

theorem momentScalarAmp2622K01P103_radius_le :
    (momentScalarAmp2622K01P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P103Expected]

def momentScalarGrow2622K01P103Input : RatPair2542 := (momentPanelGrowth2622K01P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P103Expected : RatState2542 :=
  ((((583849971282646752464318955085708694753428092709545804125518047296348638267124838670420630170093 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((370058851770609100722108164911678263139882110173 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P103_replay :
    compactExp2620 momentScalarGrow2622K01P103Input 20 = momentScalarGrow2622K01P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P103] using h

theorem momentScalarGrow2622K01P103_radius_le :
    (momentScalarGrow2622K01P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P103Expected]

end ConnesWeilRH.Dev
