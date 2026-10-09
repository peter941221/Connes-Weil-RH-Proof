import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P018 : ℚ := ((-824633498646185620852435249509910212859 : ℚ) / 13218046338699793615286423663096627200)

def momentPanelGrowth2622K05P018 : ℚ := ((172429446242479283435243537343777804489 : ℚ) / 91880329625022249604002245688216780800)

theorem momentPanelPhase_owner2622K05P018 :
    (momentPanelPhase2622K05P018 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-143 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P018 :
    (momentPanelGrowth2622K05P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P018Input : RatPair2542 := (momentPanelPhase2622K05P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P018Expected : RatState2542 :=
  ((((1719070486793397541624463302075275522649488927348448417651921239113189 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2420030949622005417488399 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P018_replay :
    compactExp2620 momentScalarAmp2622K05P018Input 20 = momentScalarAmp2622K05P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K05P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P018_replay] at h
  simpa only [momentPanelPhase_owner2622K05P018] using h

theorem momentScalarAmp2622K05P018_radius_le :
    (momentScalarAmp2622K05P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P018Expected]

def momentScalarGrow2622K05P018Input : RatPair2542 := (momentPanelGrowth2622K05P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P018Expected : RatState2542 :=
  ((((13951723864225558064023272284161122919821038070967719171344297271269440473508580511597831043282373 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((17685879477620397581325251882470925443711449960485 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P018_replay :
    compactExp2620 momentScalarGrow2622K05P018Input 20 = momentScalarGrow2622K05P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P018] using h

theorem momentScalarGrow2622K05P018_radius_le :
    (momentScalarGrow2622K05P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P018Expected]

end ConnesWeilRH.Dev
