import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P048 : ℚ := ((-119525298542532437708227612830098349523230313111779209 : ℚ) / 3150506556879135841448060448962815564051274897817600)

def momentPanelGrowth2622K02P048 : ℚ := ((249529849730802566377119566671221997003977184463944599 : ℚ) / 605078947552075550250886326004771509028706304026214400)

theorem momentPanelPhase_owner2622K02P048 :
    (momentPanelPhase2622K02P048 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P048 :
    (momentPanelGrowth2622K02P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P048Input : RatPair2542 := (momentPanelPhase2622K02P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P048Expected : RatState2542 :=
  ((((17827244726292575562802589059656245660213512123109768220136538017230530659487559 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5649883934803185221072094718303 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K02P048_replay :
    compactExp2620 momentScalarAmp2622K02P048Input 20 = momentScalarAmp2622K02P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K02P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P048_replay] at h
  simpa only [momentPanelPhase_owner2622K02P048] using h

theorem momentScalarAmp2622K02P048_radius_le :
    (momentScalarAmp2622K02P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P048Expected]

def momentScalarGrow2622K02P048Input : RatPair2542 := (momentPanelGrowth2622K02P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P048Expected : RatState2542 :=
  ((((3226251930925635210211169040576044098707831882205332174469011270478504277414883443447160823922313 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4089758588272616176977912624159520327709898452869 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P048_replay :
    compactExp2620 momentScalarGrow2622K02P048Input 20 = momentScalarGrow2622K02P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P048] using h

theorem momentScalarGrow2622K02P048_radius_le :
    (momentScalarGrow2622K02P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P048Expected]

end ConnesWeilRH.Dev
