import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P118 : ℚ := ((-330315769841331815563174522838604956998573300408387047 : ℚ) / 10490555990927346317754613532647679151440464235724800)

def momentPanelGrowth2622K02P118 : ℚ := ((990970798041713830547228042305431754301082099348466933 : ℚ) / 3990930941820883563902100416585573793795759653309644800)

theorem momentPanelPhase_owner2622K02P118 :
    (momentPanelPhase2622K02P118 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (57 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P118 :
    (momentPanelGrowth2622K02P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P118Input : RatPair2542 := (momentPanelPhase2622K02P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P118Expected : RatState2542 :=
  ((((45183871442678747001351951163912815929677476813103596003961787106426799323667559467 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57279081725555760158352274599978325 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P118_replay :
    compactExp2620 momentScalarAmp2622K02P118Input 20 = momentScalarAmp2622K02P118Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622K02P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P118]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P118 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P118_replay] at h
  simpa only [momentPanelPhase_owner2622K02P118] using h

theorem momentScalarAmp2622K02P118_radius_le :
    (momentScalarAmp2622K02P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P118Expected]

def momentScalarGrow2622K02P118Input : RatPair2542 := (momentPanelGrowth2622K02P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P118Expected : RatState2542 :=
  ((((2738018615861032332031879899645095748229923783047906928163115671136648098083308748337170201362435 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3470850119925373612354055798910926156567675678925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P118_replay :
    compactExp2620 momentScalarGrow2622K02P118Input 20 = momentScalarGrow2622K02P118Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P118_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P118] using h

theorem momentScalarGrow2622K02P118_radius_le :
    (momentScalarGrow2622K02P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P118Expected]

end ConnesWeilRH.Dev
