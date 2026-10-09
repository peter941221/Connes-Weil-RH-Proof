import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P017 : ℚ := ((-6595372848071796326690866154755289993 : ℚ) / 102628992594477452345173091507240960)

def momentPanelGrowth2622K05P017 : ℚ := ((14910241243652276923576036817671329601483 : ℚ) / 7375441679886443756037554997430950297600)

theorem momentPanelPhase_owner2622K05P017 :
    (momentPanelPhase2622K05P017 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-29 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P017 :
    (momentPanelGrowth2622K05P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P017Input : RatPair2542 := (momentPanelPhase2622K05P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P017Expected : RatState2542 :=
  ((((263026535416481215826578079558232659195730405416310508862084714160933 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2418185085410146042713971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P017_replay :
    compactExp2620 momentScalarAmp2622K05P017Input 20 = momentScalarAmp2622K05P017Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622K05P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P017]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P017 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P017_replay] at h
  simpa only [momentPanelPhase_owner2622K05P017] using h

theorem momentScalarAmp2622K05P017_radius_le :
    (momentScalarAmp2622K05P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P017Expected]

def momentScalarGrow2622K05P017Input : RatPair2542 := (momentPanelGrowth2622K05P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P017Expected : RatState2542 :=
  ((((16127653486161960191126638222632436322367163809917567128184509221911993014315842531161231760548981 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10222095103252366299313308916756863138851903595883 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P017_replay :
    compactExp2620 momentScalarGrow2622K05P017Input 20 = momentScalarGrow2622K05P017Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P017_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P017] using h

theorem momentScalarGrow2622K05P017_radius_le :
    (momentScalarGrow2622K05P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P017Expected]

end ConnesWeilRH.Dev
