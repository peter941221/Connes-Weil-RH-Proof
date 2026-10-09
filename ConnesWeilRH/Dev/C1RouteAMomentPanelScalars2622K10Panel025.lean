import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P025 : ℚ := ((-2481218318286442994221485611842320426759 : ℚ) / 47377680593169936943298384279004774400)

def momentPanelGrowth2622K10P025 : ℚ := ((21373081025071583225779451869265458403 : ℚ) / 18038160981007613091537487931218329600)

theorem momentPanelPhase_owner2622K10P025 :
    (momentPanelPhase2622K10P025 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-129 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P025, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P025 :
    (momentPanelGrowth2622K10P025 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (-129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P025, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P025Input : RatPair2542 := (momentPanelPhase2622K10P025 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P025Expected : RatState2542 :=
  ((((19236042693207415910036009124538060089123901674318696676844254354352617529 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((199958787514874282748125 : ℚ) / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896))

theorem momentScalarAmp2622K10P025_replay :
    compactExp2620 momentScalarAmp2622K10P025Input 20 = momentScalarAmp2622K10P025Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P025_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-129 / 200) 0) -
      (momentScalarAmp2622K10P025Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P025]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P025 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P025 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P025Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P025_replay] at h
  simpa only [momentPanelPhase_owner2622K10P025] using h

theorem momentScalarAmp2622K10P025_radius_le :
    (momentScalarAmp2622K10P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P025Expected]

def momentScalarGrow2622K10P025Input : RatPair2542 := (momentPanelGrowth2622K10P025 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P025Expected : RatState2542 :=
  ((((6985315982218819134125392662817613081238935143095294637596195000094662573738215766973174242165357 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8854929991647234755856701835744448054020634703175 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K10P025_replay :
    compactExp2620 momentScalarGrow2622K10P025Input 20 = momentScalarGrow2622K10P025Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P025_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P025Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P025]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P025 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P025 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P025Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P025_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P025] using h

theorem momentScalarGrow2622K10P025_radius_le :
    (momentScalarGrow2622K10P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P025Expected]

end ConnesWeilRH.Dev
