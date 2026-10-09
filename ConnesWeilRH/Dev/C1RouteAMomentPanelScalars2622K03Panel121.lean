import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P121 : ℚ := ((-218611434343994539136806180196604311624262579825405975 : ℚ) / 6582420686833720380724621025950049185152863181996032)

def momentPanelGrowth2622K03P121 : ℚ := ((2311963898934063634178684679337220032836848422401475 : ℚ) / 9582609516717064527499622796610443921440307205373952)

theorem momentPanelPhase_owner2622K03P121 :
    (momentPanelPhase2622K03P121 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (63 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P121, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P121 :
    (momentPanelGrowth2622K03P121 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P121, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P121Input : RatPair2542 := (momentPanelPhase2622K03P121 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P121Expected : RatState2542 :=
  ((((8055064316160474455913638108549174974671436925635126215421317818662451493290445951 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10211330534629324213216730436292667 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P121_replay :
    compactExp2620 momentScalarAmp2622K03P121Input 20 = momentScalarAmp2622K03P121Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P121_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (63 / 200) 0) -
      (momentScalarAmp2622K03P121Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P121]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P121 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P121 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P121Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P121_replay] at h
  simpa only [momentPanelPhase_owner2622K03P121] using h

theorem momentScalarAmp2622K03P121_radius_le :
    (momentScalarAmp2622K03P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P121Expected]

def momentScalarGrow2622K03P121Input : RatPair2542 := (momentPanelGrowth2622K03P121 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P121Expected : RatState2542 :=
  ((((2718813253262301045933596928281010086602561470895118655863510797707109932694644820706405062489901 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((861626114850212475494250892078534121301604892305 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P121_replay :
    compactExp2620 momentScalarGrow2622K03P121Input 20 = momentScalarGrow2622K03P121Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P121_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P121Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P121]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P121 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P121 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P121Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P121_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P121] using h

theorem momentScalarGrow2622K03P121_radius_le :
    (momentScalarGrow2622K03P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P121Expected]

end ConnesWeilRH.Dev
