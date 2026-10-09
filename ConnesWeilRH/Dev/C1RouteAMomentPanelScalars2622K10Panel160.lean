import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P160 : ℚ := ((-2389332721400776290580997879283178893549 : ℚ) / 40806179881586795725939474862335590400)

def momentPanelGrowth2622K10P160 : ℚ := ((14529262187495096564956744730478882631763 : ℚ) / 8312975781405638569714092740875753881600)

theorem momentPanelPhase_owner2622K10P160 :
    (momentPanelPhase2622K10P160 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P160 :
    (momentPanelGrowth2622K10P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P160Input : RatPair2542 := (momentPanelPhase2622K10P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P160Expected : RatState2542 :=
  ((((79481061768236077878648862142022246475284518624130109444225860493101007 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2518611481229505228419467 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K10P160_replay :
    compactExp2620 momentScalarAmp2622K10P160Input 20 = momentScalarAmp2622K10P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K10P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P160_replay] at h
  simpa only [momentPanelPhase_owner2622K10P160] using h

theorem momentScalarAmp2622K10P160_radius_le :
    (momentScalarAmp2622K10P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P160Expected]

def momentScalarGrow2622K10P160Input : RatPair2542 := (momentPanelGrowth2622K10P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P160Expected : RatState2542 :=
  ((((12264513113098553201337027240300950607779113416443434952423434663884172447967439561798443943595223 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15547091495195440449019828275473047288101359806505 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K10P160_replay :
    compactExp2620 momentScalarGrow2622K10P160Input 20 = momentScalarGrow2622K10P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P160] using h

theorem momentScalarGrow2622K10P160_radius_le :
    (momentScalarGrow2622K10P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P160Expected]

end ConnesWeilRH.Dev
