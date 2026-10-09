import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P174 : ℚ := ((-28502139321872559097800140717255266801829761426627619 : ℚ) / 272104772614391251323762220075546247751370643865600)

def momentPanelGrowth2622K01P174 : ℚ := ((970801305190517330865906449326191223080048891253211 : ℚ) / 146542656848584430787659511913226913128098509619200)

theorem momentPanelPhase_owner2622K01P174 :
    (momentPanelPhase2622K01P174 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P174 :
    (momentPanelGrowth2622K01P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P174Input : RatPair2542 := (momentPanelPhase2622K01P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P174Expected : RatState2542 :=
  ((((689581041031769170052067646457701828814640157770949 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629174706657 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P174_replay :
    compactExp2620 momentScalarAmp2622K01P174Input 20 = momentScalarAmp2622K01P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K01P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P174_replay] at h
  simpa only [momentPanelPhase_owner2622K01P174] using h

theorem momentScalarAmp2622K01P174_radius_le :
    (momentScalarAmp2622K01P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P174Expected]

def momentScalarGrow2622K01P174Input : RatPair2542 := (momentPanelGrowth2622K01P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P174Expected : RatState2542 :=
  ((((1609421355774945205492348032405323239312431569799198995812649978359422791336458681665069346122855811 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2040171058219864493632227578409274258592507847882519 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P174_replay :
    compactExp2620 momentScalarGrow2622K01P174Input 20 = momentScalarGrow2622K01P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P174] using h

theorem momentScalarGrow2622K01P174_radius_le :
    (momentScalarGrow2622K01P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P174Expected]

end ConnesWeilRH.Dev
