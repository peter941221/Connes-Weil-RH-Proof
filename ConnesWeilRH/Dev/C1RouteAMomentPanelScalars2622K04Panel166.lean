import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P166 : ℚ := ((-308230204388841424641537173982989153058494143982957079 : ℚ) / 4735893293936916077327604503827314761545229847756800)

def momentPanelGrowth2622K04P166 : ℚ := ((2272628339300384450210298537474035559798721668605096869 : ℚ) / 788461150945709135104469892047041010819061716405452800)

theorem momentPanelPhase_owner2622K04P166 :
    (momentPanelPhase2622K04P166 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (153 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P166 :
    (momentPanelGrowth2622K04P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P166Input : RatPair2542 := (momentPanelPhase2622K04P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P166Expected : RatState2542 :=
  ((((115887989648289149574363188977530813206156673785179729979863567271851 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417998553827461174110667 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P166_replay :
    compactExp2620 momentScalarAmp2622K04P166Input 20 = momentScalarAmp2622K04P166Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622K04P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P166]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P166 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P166_replay] at h
  simpa only [momentPanelPhase_owner2622K04P166] using h

theorem momentScalarAmp2622K04P166_radius_le :
    (momentScalarAmp2622K04P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P166Expected]

def momentScalarGrow2622K04P166Input : RatPair2542 := (momentPanelGrowth2622K04P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P166Expected : RatState2542 :=
  ((((38140936804685364706549896967965197287636292144428245389615744331108445376161260663892017562873493 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((48349248529579995984923742008861040918571508320477 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P166_replay :
    compactExp2620 momentScalarGrow2622K04P166Input 20 = momentScalarGrow2622K04P166Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P166_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P166] using h

theorem momentScalarGrow2622K04P166_radius_le :
    (momentScalarGrow2622K04P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P166Expected]

end ConnesWeilRH.Dev
