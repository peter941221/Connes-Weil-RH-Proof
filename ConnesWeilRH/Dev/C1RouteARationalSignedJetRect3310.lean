import ConnesWeilRH.Dev.C1RouteARationalSignedJetInterval3310
import ConnesWeilRH.Dev.C1RouteARationalCellWeight3289
import ConnesWeilRH.Dev.C1RouteARationalPhase3279
import ConnesWeilRH.Dev.C1RouteARationalCellFamily3288
import ConnesWeilRH.Dev.C1RouteAWeightedFamilyLocal2537

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def ratScalarRect3310 (q : ℚ) : RatRect3276 :=
  { reLo := q
    reHi := q
    imLo := 0
    imHi := 0 }

theorem ratScalarRect_mem3310 (q : ℚ) :
    (ratScalarRect3310 q).Mem (q : ℂ) := by
  unfold ratScalarRect3310 RatRect3276.Mem RatRect3276.toReal
    ComplexRect2427.Mem
  dsimp
  exact ⟨le_rfl, le_rfl, by norm_num, by norm_num⟩

def ratRectPowNat3310 (a : RatRect3276) : ℕ → RatRect3276
  | 0 => ratScalarRect3310 1
  | n + 1 => RatRect3276.mul (ratRectPowNat3310 a n) a

theorem ratRectPowNat_mem3310 {a : RatRect3276} {z : ℂ}
    (ha : a.Mem z) : ∀ n, (ratRectPowNat3310 a n).Mem (z ^ n)
  | 0 => by
      simpa [ratRectPowNat3310] using ratScalarRect_mem3310 (1 : ℚ)
  | n + 1 => by
      have h := RatRect3276.mem_mul (ratRectPowNat_mem3310 ha n) ha
      simpa [ratRectPowNat3310, pow_succ] using h

def ratWeightedLambdaRect3310 (family : Fin 30) : RatRect3276 :=
  { reLo := -(1 : ℚ) / 2
    reHi := -(1 : ℚ) / 2
    imLo := capturedModulationsRat3279 family
    imHi := capturedModulationsRat3279 family }

theorem ratWeightedLambdaRect_mem3310 (family : Fin 30) :
    (ratWeightedLambdaRect3310 family).Mem
      (weightedLambda2537 (-1 / 2) (capturedModulations2584 family)) := by
  unfold ratWeightedLambdaRect3310 RatRect3276.Mem RatRect3276.toReal
    ComplexRect2427.Mem weightedLambda2537
  dsimp
  rw [capturedModulationsRat_cast3279]
  norm_num

def ratWeightedPhaseRect3310 (cell : ℕ) (family : Fin 30) : RatRect3276 :=
  RatRect3276.mul
    (ratRealRect3281 (ratCellWeightInterval3289 cell))
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 cell family)) 9)

theorem ratWeightedPhaseRect_mem3310
    {cell : ℕ} (hcell : cell < 40960) (family : Fin 30)
    (hactive : |record2680Center3212 cell| <
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2) :
    (ratWeightedPhaseRect3310 cell family).Mem
      (weightedPhase2537 (-1 / 2) (capturedModulations2584 family)
        (record2680Center3212 cell)) := by
  have hweight0 := ratCellWeightInterval_mem3289 hcell
  have hweight :
      (ratRealRect3281 (ratCellWeightInterval3289 cell)).Mem
        (weightedExp2348 (-1 / 2) (record2680Center3212 cell)) := by
    apply ratRealRect3281_mem
    convert hweight0 using 1 <;> congr 1 <;> ring
  have hphase0 := record2680CanonicalPhasePowRect_mem3279
    hcell family hactive
  have hphase :
      (RatRect3276.powSq
        (ratPhaseRect3279 (record2680PhaseAngleRat3279 cell family)) 9).Mem
        (phaseCarrier2350 (capturedModulations2584 family)
          (record2680Center3212 cell)) := by
    simpa [phaseCarrier2350] using hphase0
  have hmul := RatRect3276.mem_mul hweight hphase
  simpa [ratWeightedPhaseRect3310, weightedPhase2537] using hmul

def ratBumpRect3310 (order cell : ℕ) (family : Fin 30) : RatRect3276 :=
  ratRealRect3281
    (ratBumpJetInterval3310 order
      (storedWidthRat3287 family ^ 2)
      (record2680CenterRat3279 cell))

theorem ratStoredRadius_pos3310 (family : Fin 30) :
    0 < (storedWidthRat3287 family ^ 2 : ℚ) := by
  dsimp [storedWidthRat3287]
  fin_cases family <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_four, Fin.ext_iff]

theorem ratBumpRect_mem3310
    {order cell : ℕ} (horder : order ≤ 6) (family : Fin 30) :
    (ratBumpRect3310 order cell family).Mem
      ((iteratedDeriv order
        (widthBump (C1RouteAOwnerScaleAudit.storedWidth family ^ 2))
        (record2680Center3212 cell) : ℝ) : ℂ) := by
  have hradiusQ : 0 < (storedWidthRat3287 family ^ 2 : ℚ) :=
    ratStoredRadius_pos3310 family
  have hradius : 0 < ((storedWidthRat3287 family ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hradiusQ
  have hradiusCast :
      ((storedWidthRat3287 family ^ 2 : ℚ) : ℝ) =
        C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
    norm_num [Rat.cast_pow, storedWidthRat_cast3287]
  have hcenter :
      (record2680CenterRat3279 cell : ℝ) = record2680Center3212 cell :=
    record2680CenterRat_cast3279 cell
  have hbump := ratBumpJetInterval_mem3310
    (radius := storedWidthRat3287 family ^ 2)
    (position := record2680CenterRat3279 cell) horder hradius
  apply ratRealRect3281_mem
  simpa [ratBumpRect3310, hradiusCast, hcenter] using hbump

def ratWeightedUnitJetRect3310
    (order index cell : ℕ) (family : Fin 30) : RatRect3276 :=
  RatRect3276.mul
    (RatRect3276.mul
      (ratScalarRect3310 (order.choose index : ℚ))
      (RatRect3276.mul
        (ratRectPowNat3310 (ratWeightedLambdaRect3310 family) index)
        (ratWeightedPhaseRect3310 cell family)))
    (ratBumpRect3310 (order - index) cell family)

theorem ratWeightedUnitJetRect_mem3310
    {order index cell : ℕ} (horder : order ≤ 6)
    (hindex : index < order + 1) (hcell : cell < 40960)
    (family : Fin 30) :
    (ratWeightedUnitJetRect3310 order index cell family).Mem
      ((order.choose index : ℂ) *
        iteratedDeriv index
          (weightedPhase2537 (-1 / 2) (capturedModulations2584 family))
          (record2680Center3212 cell) *
        (iteratedDeriv (order - index)
          (widthBump (C1RouteAOwnerScaleAudit.storedWidth family ^ 2))
          (record2680Center3212 cell) : ℝ)) := by
  let radiusQ : ℚ := storedWidthRat3287 family ^ 2
  let centerQ : ℚ := record2680CenterRat3279 cell
  have hradiusQ : 0 < radiusQ := by
    simpa [radiusQ] using ratStoredRadius_pos3310 family
  have hradius : 0 < (radiusQ : ℝ) := by
    exact_mod_cast hradiusQ
  have hradiusCast : (radiusQ : ℝ) =
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
    dsimp [radiusQ]
    norm_num [Rat.cast_pow, storedWidthRat_cast3287]
  have hcenterCast : (centerQ : ℝ) = record2680Center3212 cell := by
    dsimp [centerQ]
    exact record2680CenterRat_cast3279 cell
  have hsub : order - index ≤ 6 := by
    exact le_trans (Nat.sub_le order index) horder
  by_cases hactive : |centerQ| < radiusQ
  · have hactiveR : |record2680Center3212 cell| <
        C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
      have h : |(centerQ : ℝ)| < (radiusQ : ℝ) := by
        exact_mod_cast hactive
      rw [hcenterCast, hradiusCast] at h
      exact h
    have hlambda := ratWeightedLambdaRect_mem3310 family
    have hlambdaPow := ratRectPowNat_mem3310 hlambda index
    have hphase := ratWeightedPhaseRect_mem3310 hcell family hactiveR
    have hphasePow := RatRect3276.mem_mul hlambdaPow hphase
    have hchoose := ratScalarRect_mem3310 (order.choose index : ℚ)
    have hchoosePhase := RatRect3276.mem_mul hchoose hphasePow
    have hbump := ratBumpRect_mem3310
      (order := order - index) (cell := cell) hsub family
    have hterm := RatRect3276.mem_mul hchoosePhase hbump
    rw [weightedPhase2537_iteratedDeriv]
    simpa [ratWeightedUnitJetRect3310] using hterm
  · have hactiveR : ¬ |record2680Center3212 cell| <
        C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
      intro h
      apply hactive
      have h' : |(centerQ : ℝ)| < (radiusQ : ℝ) := by
        rw [hcenterCast, hradiusCast]
        exact h
      exact_mod_cast h'
    have hzero : iteratedDeriv (order - index)
        (widthBump (C1RouteAOwnerScaleAudit.storedWidth family ^ 2))
        (record2680Center3212 cell) = 0 := by
      have hderiv := widthBump_iteratedDeriv_global2350
        (order - index) hsub
        (by simpa [hradiusCast] using hradius)
        (position := record2680Center3212 cell)
      rw [hderiv, if_neg hactiveR]
    rw [hzero]
    unfold ratWeightedUnitJetRect3310 ratBumpRect3310 ratBumpJetInterval3310
    dsimp [radiusQ, centerQ] at hactive
    rw [if_neg hactive]
    rw [ratRect_mul_zero_real3288]
    norm_num [RatRect3276.Mem, RatRect3276.toReal,
      ComplexRect2427.Mem]

def ratWeightedUnitJetSumRect3310
    (order cell : ℕ) (family : Fin 30) : RatRect3276 :=
  RatRect3276.sumFinset
    (fun index => ratWeightedUnitJetRect3310 order index cell family)
    (Finset.range (order + 1))

theorem ratWeightedUnitJetSumRect_mem3310
    {order cell : ℕ} (horder : order ≤ 6)
    (hcell : cell < 40960) (family : Fin 30) :
    (ratWeightedUnitJetSumRect3310 order cell family).Mem
      (weightedUnitJet2539 order (-1 / 2) capturedModulations2584
        family (record2680Center3212 cell)) := by
  have hradius : 0 <
      (C1RouteAOwnerScaleAudit.storedWidth family ^ 2 : ℝ) := by
    have hq := ratStoredRadius_pos3310 family
    have hq' : 0 <
        ((storedWidthRat3287 family ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hq
    simpa [Rat.cast_pow, storedWidthRat_cast3287] using hq'
  have hderiv := weightedExternalFamily_iteratedDeriv2537 order
    (-1 / 2) (1 : ℂ) (capturedModulations2584 family)
    (radius := C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
    (position := record2680Center3212 cell) hradius
  have hterm : ∀ index ∈ Finset.range (order + 1),
      (ratWeightedUnitJetRect3310 order index cell family).Mem
        ((order.choose index : ℂ) *
          iteratedDeriv index
            (weightedPhase2537 (-1 / 2) (capturedModulations2584 family))
            (record2680Center3212 cell) *
          (iteratedDeriv (order - index)
            (widthBump (C1RouteAOwnerScaleAudit.storedWidth family ^ 2))
            (record2680Center3212 cell) : ℝ)) := by
    intro index hindex
    apply ratWeightedUnitJetRect_mem3310 horder
    · simpa using hindex
    · exact hcell
  have hsum := RatRect3276.mem_sumFinset
    (s := Finset.range (order + 1)) hterm
  simp only [weightedUnitJet2539]
  rw [hderiv]
  simp only [one_mul]
  simpa [ratWeightedUnitJetSumRect3310] using hsum

def ratWeightedPhysicalTermRect3310
    (order cell : ℕ) (family : Fin 30) : RatRect3276 :=
  RatRect3276.mul
    (ratCoefficientRect3282 family)
    (ratWeightedUnitJetSumRect3310 order cell family)

def ratWeightedPhysicalRect3310 (order cell : ℕ) : RatRect3276 :=
  RatRect3276.sumFinset
    (fun family => ratWeightedPhysicalTermRect3310 order cell family)
    (Finset.univ : Finset (Fin 30))

theorem ratWeightedPhysicalRect_mem3310
    {order cell : ℕ} (horder : order ≤ 6)
    (hcell : cell < 40960) :
    (ratWeightedPhysicalRect3310 order cell).Mem
      (iteratedDeriv order
        (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584)
        (record2680Center3212 cell)) := by
  have hterm : ∀ family : Fin 30,
      (ratWeightedPhysicalTermRect3310 order cell family).Mem
        (record2680CorrectionCoefficient family *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584
            family (record2680Center3212 cell)) := by
    intro family
    exact RatRect3276.mem_mul
      (ratCoefficientRect_mem3282 family)
      (ratWeightedUnitJetSumRect_mem3310 horder hcell family)
  have hsum := RatRect3276.mem_sumFinset
    (s := (Finset.univ : Finset (Fin 30)))
    (fun (family : Fin 30) _ => hterm family)
  rw [weightedPhysical2539_iteratedDeriv]
  simpa [ratWeightedPhysicalRect3310, ratWeightedPhysicalTermRect3310] using hsum

def ratWeightedPhysicalBlockRect3310 (order block : ℕ) : RatRect3276 :=
  RatRect3276.sumFinset
    (fun offset => ratWeightedPhysicalRect3310 order (block * 256 + offset))
    (Finset.range 256)

theorem ratWeightedPhysicalBlockRect_mem3310
    {order block : ℕ} (horder : order ≤ 6) (hblock : block < 160) :
    (ratWeightedPhysicalBlockRect3310 order block).Mem
      (∑ offset ∈ Finset.range 256,
        iteratedDeriv order
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584)
          (record2680Center3212 (block * 256 + offset))) := by
  have hterm : ∀ offset ∈ Finset.range 256,
      (ratWeightedPhysicalRect3310 order (block * 256 + offset)).Mem
        (iteratedDeriv order
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584)
          (record2680Center3212 (block * 256 + offset))) := by
    intro offset hoff
    apply ratWeightedPhysicalRect_mem3310 horder
    have hoff' : offset < 256 := Finset.mem_range.mp hoff
    nlinarith
  exact RatRect3276.mem_sumFinset hterm

end ConnesWeilRH.Dev
