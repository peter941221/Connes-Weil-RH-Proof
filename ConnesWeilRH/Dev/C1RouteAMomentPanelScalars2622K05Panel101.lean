import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P101 : ℚ := ((-806965636959852975627005879830359916621 : ℚ) / 26685566315524502776787398517011251200)

def momentPanelGrowth2622K05P101 : ℚ := ((530509923397396727095551220791516681 : ℚ) / 6012720327002537697179162643739443200)

theorem momentPanelPhase_owner2622K05P101 :
    (momentPanelPhase2622K05P101 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P101 :
    (momentPanelGrowth2622K05P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P101Input : RatPair2542 := (momentPanelPhase2622K05P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P101Expected : RatState2542 :=
  ((((157263997524879438383901403214058058883847879867386387467628495543934924705038225239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((199361550144206125637323138644407017 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P101_replay :
    compactExp2620 momentScalarAmp2622K05P101Input 20 = momentScalarAmp2622K05P101Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622K05P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P101]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P101 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P101_replay] at h
  simpa only [momentPanelPhase_owner2622K05P101] using h

theorem momentScalarAmp2622K05P101_radius_le :
    (momentScalarAmp2622K05P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P101Expected]

def momentScalarGrow2622K05P101Input : RatPair2542 := (momentPanelGrowth2622K05P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P101Expected : RatState2542 :=
  ((((583252988691244646905857495861514278645624145963042632884776727874264180593366835254511368875599 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1478721877973311052991818448714309769790104030777 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P101_replay :
    compactExp2620 momentScalarGrow2622K05P101Input 20 = momentScalarGrow2622K05P101Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P101_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P101] using h

theorem momentScalarGrow2622K05P101_radius_le :
    (momentScalarGrow2622K05P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P101Expected]

end ConnesWeilRH.Dev
