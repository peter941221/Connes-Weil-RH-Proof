import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P097 : ℚ := ((-684761768486158626554201709272974292366134837948971 : ℚ) / 22707510790951821707637329773941467619849498787840)

def momentPanelGrowth2622K01P097 : ℚ := ((231548273368255938293376542710270386812385663945331 : ℚ) / 4586710228856825620759987162870606282414823256883200)

theorem momentPanelPhase_owner2622K01P097 :
    (momentPanelPhase2622K01P097 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P097, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P097 :
    (momentPanelGrowth2622K01P097 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P097, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P097Input : RatPair2542 := (momentPanelPhase2622K01P097 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P097Expected : RatState2542 :=
  ((((42762942462966379743065051180870165183885256683365131008896155435467631374095830341 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((216840114687031137832111002802357047 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P097_replay :
    compactExp2620 momentScalarAmp2622K01P097Input 20 = momentScalarAmp2622K01P097Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P097_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 40) 0) -
      (momentScalarAmp2622K01P097Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P097]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P097 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P097 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P097Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P097_replay] at h
  simpa only [momentPanelPhase_owner2622K01P097] using h

theorem momentScalarAmp2622K01P097_radius_le :
    (momentScalarAmp2622K01P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P097Expected]

def momentScalarGrow2622K01P097Input : RatPair2542 := (momentPanelGrowth2622K01P097 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P097Expected : RatState2542 :=
  ((((280823123675771479761201244664491082714351284312385951862549459979272304489115442945082827278369 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1423942336588241146386219640279233872322191958079 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P097_replay :
    compactExp2620 momentScalarGrow2622K01P097Input 20 = momentScalarGrow2622K01P097Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P097_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P097Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P097]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P097 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P097 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P097Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P097_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P097] using h

theorem momentScalarGrow2622K01P097_radius_le :
    (momentScalarGrow2622K01P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P097Expected]

end ConnesWeilRH.Dev
