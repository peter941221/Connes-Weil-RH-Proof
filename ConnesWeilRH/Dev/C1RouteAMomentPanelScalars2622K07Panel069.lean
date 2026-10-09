import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P069 : ℚ := ((-34166971539785833027269741666466534975 : ℚ) / 1036268871469771145300312962705129472)

def momentPanelGrowth2622K07P069 : ℚ := ((810371915892333651999423780394464672075 : ℚ) / 3706589301926174179542460115272589115392)

theorem momentPanelPhase_owner2622K07P069 :
    (momentPanelPhase2622K07P069 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-41 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P069, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P069 :
    (momentPanelGrowth2622K07P069 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P069, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P069Input : RatPair2542 := (momentPanelPhase2622K07P069 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P069Expected : RatState2542 :=
  ((((2560661381211399900920734801516425621028626507680837063076001118742235481893311605 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((12984504024791101884088335039021197 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P069_replay :
    compactExp2620 momentScalarAmp2622K07P069Input 20 = momentScalarAmp2622K07P069Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P069_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-41 / 200) 0) -
      (momentScalarAmp2622K07P069Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P069]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P069 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P069 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P069Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P069_replay] at h
  simpa only [momentPanelPhase_owner2622K07P069] using h

theorem momentScalarAmp2622K07P069_radius_le :
    (momentScalarAmp2622K07P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P069Expected]

def momentScalarGrow2622K07P069Input : RatPair2542 := (momentPanelGrowth2622K07P069 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P069Expected : RatState2542 :=
  ((((2657960054653396212450341653067440834295310125034834083073981857785528323455044304958046390124221 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3369363956145201715347014102521181316689284572645 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P069_replay :
    compactExp2620 momentScalarGrow2622K07P069Input 20 = momentScalarGrow2622K07P069Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P069_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P069Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P069]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P069 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P069 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P069Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P069_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P069] using h

theorem momentScalarGrow2622K07P069_radius_le :
    (momentScalarGrow2622K07P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P069Expected]

end ConnesWeilRH.Dev
