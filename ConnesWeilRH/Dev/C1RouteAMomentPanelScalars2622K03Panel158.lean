import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P158 : ℚ := ((-72812908998166206967101116708624729403289782223229675 : ℚ) / 1292880885923849994015934695141641866263129325830144)

def momentPanelGrowth2622K03P158 : ℚ := ((3789057381146038012573066286373217251060383691924874425 : ℚ) / 2507125767594963089699352515589286169421359929681248256)

theorem momentPanelPhase_owner2622K03P158 :
    (momentPanelPhase2622K03P158 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (137 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P158 :
    (momentPanelGrowth2622K03P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P158Input : RatPair2542 := (momentPanelPhase2622K03P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P158Expected : RatState2542 :=
  ((((185691956157527267952019311033798110417190233344166171440233125940199857 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3359472290436390191180313 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P158_replay :
    compactExp2620 momentScalarAmp2622K03P158Input 20 = momentScalarAmp2622K03P158Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622K03P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P158]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P158 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P158_replay] at h
  simpa only [momentPanelPhase_owner2622K03P158] using h

theorem momentScalarAmp2622K03P158_radius_le :
    (momentScalarAmp2622K03P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P158Expected]

def momentScalarGrow2622K03P158Input : RatPair2542 := (momentPanelGrowth2622K03P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P158Expected : RatState2542 :=
  ((((9681763764307553277083362621375585751592266666785742220859414642404485232930981086585501489292267 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12273075957864235106825320188944433406942063457839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P158_replay :
    compactExp2620 momentScalarGrow2622K03P158Input 20 = momentScalarGrow2622K03P158Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P158_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P158] using h

theorem momentScalarGrow2622K03P158_radius_le :
    (momentScalarGrow2622K03P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P158Expected]

end ConnesWeilRH.Dev
