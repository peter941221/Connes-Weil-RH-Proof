import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P065 : ℚ := ((-73241143422392523244294616078891072326784404027695725 : ℚ) / 2289625002583525784230847751054146885668475320139776)

def momentPanelGrowth2622K03P065 : ℚ := ((5947409186675722915935171457241450441403813331279 : ℚ) / 34253944624943037145398863266787883273185918976000)

theorem momentPanelPhase_owner2622K03P065 :
    (momentPanelPhase2622K03P065 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-49 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P065, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P065 :
    (momentPanelGrowth2622K03P065 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P065, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P065Input : RatPair2542 := (momentPanelPhase2622K03P065 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P065Expected : RatState2542 :=
  ((((6842414083739850506471570788279728814242441219769435588180861868135200399375567825 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((34696219723797350988927961416201049 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P065_replay :
    compactExp2620 momentScalarAmp2622K03P065Input 20 = momentScalarAmp2622K03P065Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P065_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-49 / 200) 0) -
      (momentScalarAmp2622K03P065Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P065]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P065 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P065 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P065Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P065_replay] at h
  simpa only [momentPanelPhase_owner2622K03P065] using h

theorem momentScalarAmp2622K03P065_radius_le :
    (momentScalarAmp2622K03P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P065Expected]

def momentScalarGrow2622K03P065Input : RatPair2542 := (momentPanelGrowth2622K03P065 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P065Expected : RatState2542 :=
  ((((2540995258708698747407214255186769856468785638944829001896330078338189081327850638007466312101257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3221093631518850503139596660925679288128343592957 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P065_replay :
    compactExp2620 momentScalarGrow2622K03P065Input 20 = momentScalarGrow2622K03P065Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P065_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P065Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P065]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P065 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P065 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P065Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P065_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P065] using h

theorem momentScalarGrow2622K03P065_radius_le :
    (momentScalarGrow2622K03P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P065Expected]

end ConnesWeilRH.Dev
