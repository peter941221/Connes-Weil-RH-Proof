import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P108 : ℚ := ((-804477794715661450040433539021903287039 : ℚ) / 26117658846622256004916875481002803200)

def momentPanelGrowth2622K05P108 : ℚ := ((4296879332659461692549558722485726426523 : ℚ) / 31407419782145991187919086734190156185600)

theorem momentPanelPhase_owner2622K05P108 :
    (momentPanelPhase2622K05P108 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (37 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P108 :
    (momentPanelGrowth2622K05P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P108Input : RatPair2542 := (momentPanelPhase2622K05P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P108Expected : RatState2542 :=
  ((((89625638507231872535032190136399575893152459181082916844896696669949043198313719405 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((113617331927638156729173517554734877 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P108_replay :
    compactExp2620 momentScalarAmp2622K05P108Input 20 = momentScalarAmp2622K05P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K05P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P108_replay] at h
  simpa only [momentPanelPhase_owner2622K05P108] using h

theorem momentScalarAmp2622K05P108_radius_le :
    (momentScalarAmp2622K05P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P108Expected]

def momentScalarGrow2622K05P108Input : RatPair2542 := (momentPanelGrowth2622K05P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P108Expected : RatState2542 :=
  ((((612286758369461103876639517551821209287995859393038064826647387129461961892212700411052408420995 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3104662301960431780532462190400917520917342380441 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P108_replay :
    compactExp2620 momentScalarGrow2622K05P108Input 20 = momentScalarGrow2622K05P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P108] using h

theorem momentScalarGrow2622K05P108_radius_le :
    (momentScalarGrow2622K05P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P108Expected]

end ConnesWeilRH.Dev
