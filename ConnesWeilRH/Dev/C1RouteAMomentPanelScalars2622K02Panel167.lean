import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P167 : ℚ := ((-874908513014551318480125348613137761978002722545563 : ℚ) / 12160150341854778186616596459709698561981001236480)

def momentPanelGrowth2622K02P167 : ℚ := ((423062671851838997778968056176163835615234224884038439 : ℚ) / 136793270584479289436138466284514356800981605705318400)

theorem momentPanelPhase_owner2622K02P167 :
    (momentPanelPhase2622K02P167 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P167 :
    (momentPanelGrowth2622K02P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P167Input : RatPair2542 := (momentPanelPhase2622K02P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P167Expected : RatState2542 :=
  ((((120954353248184813108729136286137006070210917333341046159960846153 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925896283819530822283 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P167_replay :
    compactExp2620 momentScalarAmp2622K02P167Input 20 = momentScalarAmp2622K02P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K02P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P167_replay] at h
  simpa only [momentPanelPhase_owner2622K02P167] using h

theorem momentScalarAmp2622K02P167_radius_le :
    (momentScalarAmp2622K02P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P167Expected]

def momentScalarGrow2622K02P167Input : RatPair2542 := (momentPanelGrowth2622K02P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P167Expected : RatState2542 :=
  ((((47070401169947259421295390171700238996890729346923533843747198543415615049254628795426537308172525 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((59668646306514681258827388944634296343820987146867 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P167_replay :
    compactExp2620 momentScalarGrow2622K02P167Input 20 = momentScalarGrow2622K02P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P167] using h

theorem momentScalarGrow2622K02P167_radius_le :
    (momentScalarGrow2622K02P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P167Expected]

end ConnesWeilRH.Dev
