import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K15
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K15P179 : ℚ := ((-803837477454333253219260338418821011697 : ℚ) / 5380923267848788163473205766180044800)

def momentPanelGrowth2622K15P179 : ℚ := ((5481920710962892511094735533286218209 : ℚ) / 366097493345912651152247885712588800)

theorem momentPanelPhase_owner2622K15P179 :
    (momentPanelPhase2622K15P179 : ℝ) = momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (179 / 200) 0 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P179, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K15P179 :
    (momentPanelGrowth2622K15P179 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2))
      (179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P179, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K15P179Input : RatPair2542 := (momentPanelPhase2622K15P179 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K15P179Expected : RatState2542 :=
  ((((28304218294845785096456274261287 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K15P179_replay :
    compactExp2620 momentScalarAmp2622K15P179Input 20 = momentScalarAmp2622K15P179Expected := by
  decide +kernel

theorem momentScalarAmp2622K15P179_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (179 / 200) 0) -
      (momentScalarAmp2622K15P179Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K15P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K15P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P179]
  have h := compactExp_real_error2620 momentPanelPhase2622K15P179 20 hsmall
  change |Real.exp (momentPanelPhase2622K15P179 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K15P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K15P179Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K15P179_replay] at h
  simpa only [momentPanelPhase_owner2622K15P179] using h

theorem momentScalarAmp2622K15P179_radius_le :
    (momentScalarAmp2622K15P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarAmp2622K15P179Expected]

def momentScalarGrow2622K15P179Input : RatPair2542 := (momentPanelGrowth2622K15P179 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K15P179Expected : RatState2542 :=
  ((((1700735298592640509978836880910584116927163963786461563551559372722584755106615787959906826393788471657 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((8623629339822289788400557353952360288661749107792211703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K15P179_replay :
    compactExp2620 momentScalarGrow2622K15P179Input 20 = momentScalarGrow2622K15P179Expected := by
  decide +kernel

theorem momentScalarGrow2622K15P179_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K15P179Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K15P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K15P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P179]
  have h := compactExp_real_error2620 momentPanelGrowth2622K15P179 20 hsmall
  change |Real.exp (momentPanelGrowth2622K15P179 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K15P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K15P179Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K15P179_replay] at h
  simpa only [momentPanelGrowth_owner2622K15P179] using h

theorem momentScalarGrow2622K15P179_radius_le :
    (momentScalarGrow2622K15P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarGrow2622K15P179Expected]

end ConnesWeilRH.Dev
