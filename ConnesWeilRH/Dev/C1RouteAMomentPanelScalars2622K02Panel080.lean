import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P080 : ℚ := ((-115644731893853426213262796226419332823528280762179913 : ℚ) / 3771644752744769581684626502867235847405046228582400)

def momentPanelGrowth2622K02P080 : ℚ := ((47608643647621884071654808270322527652359213357293 : ℚ) / 466281821207037093141742026219150061056243322060800)

theorem momentPanelPhase_owner2622K02P080 :
    (momentPanelPhase2622K02P080 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P080 :
    (momentPanelGrowth2622K02P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P080Input : RatPair2542 := (momentPanelPhase2622K02P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P080Expected : RatState2542 :=
  ((((103139961394351277057994553382773049443092277672138086034899576779118135694857584187 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((130749257180490597193851082783788135 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P080_replay :
    compactExp2620 momentScalarAmp2622K02P080Input 20 = momentScalarAmp2622K02P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K02P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P080_replay] at h
  simpa only [momentPanelPhase_owner2622K02P080] using h

theorem momentScalarAmp2622K02P080_radius_le :
    (momentScalarAmp2622K02P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P080Expected]

def momentScalarGrow2622K02P080Input : RatPair2542 := (momentPanelGrowth2622K02P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P080Expected : RatState2542 :=
  ((((2365599728510530666454532687824143278582541168993434274963997437543869239437238353014389160926077 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2998753623749225847154586127500758113331809346795 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P080_replay :
    compactExp2620 momentScalarGrow2622K02P080Input 20 = momentScalarGrow2622K02P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P080] using h

theorem momentScalarGrow2622K02P080_radius_le :
    (momentScalarGrow2622K02P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P080Expected]

end ConnesWeilRH.Dev
