import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P013 : ℚ := ((-376848688110019318266440091352768512405224235537042921 : ℚ) / 4735893293936916077327604503827314761545229847756800)

def momentPanelGrowth2622K04P013 : ℚ := ((2272628339300384450210298537474035559798721668605096869 : ℚ) / 788461150945709135104469892047041010819061716405452800)

theorem momentPanelPhase_owner2622K04P013 :
    (momentPanelPhase2622K04P013 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P013 :
    (momentPanelGrowth2622K04P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P013Input : RatPair2542 := (momentPanelPhase2622K04P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P013Expected : RatState2542 :=
  ((((461662050577674741391382686129650611960197901193662235595405 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((302231454913021626264471 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P013_replay :
    compactExp2620 momentScalarAmp2622K04P013Input 20 = momentScalarAmp2622K04P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K04P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P013_replay] at h
  simpa only [momentPanelPhase_owner2622K04P013] using h

theorem momentScalarAmp2622K04P013_radius_le :
    (momentScalarAmp2622K04P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P013Expected]

def momentScalarGrow2622K04P013Input : RatPair2542 := (momentPanelGrowth2622K04P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P013Expected : RatState2542 :=
  ((((38140936804685364706549896967965197287636292144428245389615744331108445376161260663892017562873493 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((48349248529579995984923742008861040918571508320477 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P013_replay :
    compactExp2620 momentScalarGrow2622K04P013Input 20 = momentScalarGrow2622K04P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P013] using h

theorem momentScalarGrow2622K04P013_radius_le :
    (momentScalarGrow2622K04P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P013Expected]

end ConnesWeilRH.Dev
