import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P000 : ℚ := ((-116950889323721085024122140473495394887545974741847273 : ℚ) / 757297625749782312889526535389902119364685358694400)

def momentPanelGrowth2622K02P000 : ℚ := ((772820271360102471005213805530937069881093414302119 : ℚ) / 51523641706685151706204123497126774423417153126400)

theorem momentPanelPhase_owner2622K02P000 :
    (momentPanelPhase2622K02P000 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-179 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P000, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P000 :
    (momentPanelGrowth2622K02P000 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P000, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P000Input : RatPair2542 := (momentPanelPhase2622K02P000 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P000Expected : RatState2542 :=
  ((((182259075909609383928274529061 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P000_replay :
    compactExp2620 momentScalarAmp2622K02P000Input 20 = momentScalarAmp2622K02P000Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P000_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-179 / 200) 0) -
      (momentScalarAmp2622K02P000Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P000]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P000 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P000 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P000Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P000_replay] at h
  simpa only [momentPanelPhase_owner2622K02P000] using h

theorem momentScalarAmp2622K02P000_radius_le :
    (momentScalarAmp2622K02P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P000Expected]

def momentScalarGrow2622K02P000Input : RatPair2542 := (momentPanelGrowth2622K02P000 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P000Expected : RatState2542 :=
  ((((6977924529764417699700722678872311785007402671455668319284322328577239972605112767242593032780558940559 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4422721844067930779875645099000661387007412957149030767 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P000_replay :
    compactExp2620 momentScalarGrow2622K02P000Input 20 = momentScalarGrow2622K02P000Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P000_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P000Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P000]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P000 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P000 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P000Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P000_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P000] using h

theorem momentScalarGrow2622K02P000_radius_le :
    (momentScalarGrow2622K02P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P000Expected]

end ConnesWeilRH.Dev
