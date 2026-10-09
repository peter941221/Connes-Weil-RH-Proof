import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P079 : ℚ := ((-347386997701944796993992567534174940322102198511674781 : ℚ) / 11292098295151013386956946933090515620033014739763200)

def momentPanelGrowth2622K02P079 : ℚ := ((503823485511550212366752808574343386805976150289139413 : ℚ) / 4643057539590549105076203975458681515550673178774732800)

theorem momentPanelPhase_owner2622K02P079 :
    (momentPanelPhase2622K02P079 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P079 :
    (momentPanelGrowth2622K02P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P079Input : RatPair2542 := (momentPanelPhase2622K02P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P079Expected : RatState2542 :=
  ((((93128572359168569029519793418807725234602310648206646174822238786720507943415401271 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((59028977126546812311931581855456335 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P079_replay :
    compactExp2620 momentScalarAmp2622K02P079Input 20 = momentScalarAmp2622K02P079Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622K02P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P079]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P079 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P079_replay] at h
  simpa only [momentPanelPhase_owner2622K02P079] using h

theorem momentScalarAmp2622K02P079_radius_le :
    (momentScalarAmp2622K02P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P079Expected]

def momentScalarGrow2622K02P079Input : RatPair2542 := (momentPanelGrowth2622K02P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P079Expected : RatState2542 :=
  ((((2380808166509429457426747154650060953458067490695942212125101521481713450650368377298472620441397 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3018032588984969415098866155805504912134999247031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P079_replay :
    compactExp2620 momentScalarGrow2622K02P079Input 20 = momentScalarGrow2622K02P079Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P079_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P079] using h

theorem momentScalarGrow2622K02P079_radius_le :
    (momentScalarGrow2622K02P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P079Expected]

end ConnesWeilRH.Dev
