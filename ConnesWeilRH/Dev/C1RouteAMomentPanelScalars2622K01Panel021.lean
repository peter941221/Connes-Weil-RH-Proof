import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P021 : ℚ := ((-28609371886675519475070336318618135831235285538170877 : ℚ) / 505031596064003903912474490289703854009034892902400)

def momentPanelGrowth2622K01P021 : ℚ := ((1479024982555872860829572048796631999614663659487300033 : ℚ) / 979346002966782456913809576402064909930218722531737600)

theorem momentPanelPhase_owner2622K01P021 :
    (momentPanelPhase2622K01P021 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-137 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P021 :
    (momentPanelGrowth2622K01P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P021Input : RatPair2542 := (momentPanelPhase2622K01P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P021Expected : RatState2542 :=
  ((((533814880010499016515007545354213221883227953040033639223419921263568401 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((386822368884930266418533 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P021_replay :
    compactExp2620 momentScalarAmp2622K01P021Input 20 = momentScalarAmp2622K01P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K01P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P021_replay] at h
  simpa only [momentPanelPhase_owner2622K01P021] using h

theorem momentScalarAmp2622K01P021_radius_le :
    (momentScalarAmp2622K01P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P021Expected]

def momentScalarGrow2622K01P021Input : RatPair2542 := (momentPanelGrowth2622K01P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P021Expected : RatState2542 :=
  ((((9671136700672359492970621822796626332255715056227824586165237192059900514806073091839564933675199 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12259604586525031867485708576834603952227704958107 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P021_replay :
    compactExp2620 momentScalarGrow2622K01P021Input 20 = momentScalarGrow2622K01P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P021] using h

theorem momentScalarGrow2622K01P021_radius_le :
    (momentScalarGrow2622K01P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P021Expected]

end ConnesWeilRH.Dev
