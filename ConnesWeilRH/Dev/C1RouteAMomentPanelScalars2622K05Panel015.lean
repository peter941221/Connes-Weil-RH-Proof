import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P015 : ℚ := ((-823947788540868067975877608847360074513 : ℚ) / 12033553617846536062527904187993292800)

def momentPanelGrowth2622K05P015 : ℚ := ((117527931459634116089306964929365521 : ℚ) / 49691903528946592538670765650739200)

theorem momentPanelPhase_owner2622K05P015 :
    (momentPanelPhase2622K05P015 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-149 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P015, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P015 :
    (momentPanelGrowth2622K05P015 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P015, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P015Input : RatPair2542 := (momentPanelPhase2622K05P015 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P015Expected : RatState2542 :=
  ((((3918150342838619691225536462394062326855316764684689592732993762537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208928303199619470318917 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P015_replay :
    compactExp2620 momentScalarAmp2622K05P015Input 20 = momentScalarAmp2622K05P015Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P015_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-149 / 200) 0) -
      (momentScalarAmp2622K05P015Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P015]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P015 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P015 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P015Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P015_replay] at h
  simpa only [momentPanelPhase_owner2622K05P015] using h

theorem momentScalarAmp2622K05P015_radius_le :
    (momentScalarAmp2622K05P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P015Expected]

def momentScalarGrow2622K05P015Input : RatPair2542 := (momentPanelGrowth2622K05P015 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P015Expected : RatState2542 :=
  ((((710579359155423843267569639350225213130160462942637623175537678253604180445152512869276829299077 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((28824458221039042828685690600047681592239480983977 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P015_replay :
    compactExp2620 momentScalarGrow2622K05P015Input 20 = momentScalarGrow2622K05P015Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P015_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P015Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P015]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P015 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P015 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P015Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P015_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P015] using h

theorem momentScalarGrow2622K05P015_radius_le :
    (momentScalarGrow2622K05P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P015Expected]

end ConnesWeilRH.Dev
